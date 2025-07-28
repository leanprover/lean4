// Lean compiler output
// Module: Lake.Build.Run
// Imports: Lake.Util.Lock Lake.Build.Index Lake.Build.Job
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
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__6;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_save(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__0;
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__4;
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__20;
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__2;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__3;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__13;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0;
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__2;
LEAN_EXPORT lean_object* l_Lake_print_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__3;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__17;
uint64_t lean_string_hash(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Package_inputsFileIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__6;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__4;
static lean_object* l_Lake_Monitor_print___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_saveInputs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__5;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__6;
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__16;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__0;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
static lean_object* l_Lake_print_x21___closed__7;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__5;
static lean_object* l_Lake_Monitor_print___closed__0;
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__19;
uint8_t l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_266_(uint8_t, uint8_t);
lean_object* lean_io_mono_ms_now(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__6;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_print_x21___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lake_print_x21___closed__8;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__0;
static lean_object* l_Lake_print_x21___closed__6;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__4;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_main___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_print___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__11;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lake_Cache_isDisabled(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__2;
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__23;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__9;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__18;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__7;
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__24;
static lean_object* l_Lake_Ansi_resetLine___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__12;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Monitor_main___lam__0(uint8_t, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__3;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__5;
static lean_object* l_Lake_mkBuildContext___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__5;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__7;
static lean_object* l_Lake_Monitor_poll___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__21;
uint8_t l_Lake_ordLogLevel____x40_Lake_Util_Log___hyg_760_(uint8_t, uint8_t);
lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lean_Meta_realizeConst_realizeAndReport_spec__1_spec__3(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_mkBuildContext___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__25;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__8;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_resetLine;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1;
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_poll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_print_x21___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__8;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__15;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__14;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__0;
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__9;
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__2;
LEAN_EXPORT lean_object* l_Lake_flush(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_recFetch___at___Lake_recFetchAcyclic___at___Lake_recFetchWithIndex_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__3;
static lean_object* l_Lake_Monitor_print___closed__2;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__22;
static lean_object* _init_l_Lake_mkBuildContext___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore;
x_2 = l_Lake_mkBuildContext___closed__1;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", commit ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mkBuildContext___closed__3;
x_2 = l_Lake_mkBuildContext___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__6() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_mkBuildContext___closed__5;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lake_mkBuildContext___closed__0;
x_5 = lean_st_mk_ref(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = l_Lake_Env_leanGithash(x_8);
lean_dec_ref(x_8);
x_10 = 1723;
x_11 = lean_string_hash(x_9);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = l_Lake_mkBuildContext___closed__4;
x_14 = lean_string_append(x_13, x_9);
lean_dec_ref(x_9);
x_15 = l_Lake_mkBuildContext___closed__6;
x_16 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*3, x_12);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = l_Lake_Env_leanGithash(x_20);
lean_dec_ref(x_20);
x_22 = 1723;
x_23 = lean_string_hash(x_21);
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = l_Lake_mkBuildContext___closed__4;
x_26 = lean_string_append(x_25, x_21);
lean_dec_ref(x_21);
x_27 = l_Lake_mkBuildContext___closed__6;
x_28 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint64(x_28, sizeof(void*)*3, x_24);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_18);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
return x_30;
}
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10494;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__0;
x_2 = l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10487;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__1;
x_2 = l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10479;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__2;
x_2 = l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10463;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__3;
x_2 = l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10367;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__4;
x_2 = l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10431;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__5;
x_2 = l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10491;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__6;
x_2 = l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10493;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__7;
x_2 = l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_3, x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_4, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Ansi_resetLine___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\x1b[2K\r", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Ansi_resetLine() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Ansi_resetLine___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_print_x21___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_print_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_print_x21___closed__0;
x_3 = l_instInhabitedOfMonad___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_print_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.print!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("print!", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_print_x21___closed__6;
x_2 = l_Lake_print_x21___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_print_x21___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" failed: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_print_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_2);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_13 = l_Lake_print_x21___closed__1;
x_14 = l_Lake_print_x21___closed__2;
x_15 = l_Lake_print_x21___closed__3;
x_16 = lean_unsigned_to_nat(79u);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lake_print_x21___closed__4;
x_19 = l_Lake_print_x21___closed__7;
x_20 = 1;
x_21 = l_Lean_Name_toString(x_19, x_20, x_12);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = l_Lake_print_x21___closed__8;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_io_error_to_string(x_10);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
x_27 = l_Lake_print_x21___closed__9;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_String_quote(x_2);
lean_dec_ref(x_2);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_unsigned_to_nat(120u);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_format_pretty(x_30, x_31, x_32, x_32);
x_34 = lean_string_append(x_28, x_33);
lean_dec_ref(x_33);
x_35 = l_mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_34);
lean_dec_ref(x_34);
x_36 = l_panic___redArg(x_13, x_35);
x_37 = lean_apply_1(x_36, x_11);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_print_x21___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_print_x21___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_print___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_print___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Monitor_print___closed__0;
x_2 = 1;
x_3 = l_Lake_print_x21___closed__7;
x_4 = l_Lean_Name_toString(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Monitor_print___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Monitor_print___closed__1;
x_2 = l_Lake_print_x21___closed__4;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_print___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_print_x21___closed__8;
x_2 = l_Lake_Monitor_print___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
lean_inc_ref(x_1);
x_12 = lean_apply_2(x_11, x_1, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_5 = x_13;
x_6 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec_ref(x_12);
x_17 = l_Lake_print_x21___closed__1;
x_18 = l_Lake_print_x21___closed__2;
x_19 = l_Lake_print_x21___closed__3;
x_20 = lean_unsigned_to_nat(79u);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lake_Monitor_print___closed__3;
x_23 = lean_io_error_to_string(x_15);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l_Lake_print_x21___closed__9;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_String_quote(x_1);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unsigned_to_nat(120u);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_format_pretty(x_28, x_29, x_30, x_30);
x_32 = lean_string_append(x_26, x_31);
lean_dec_ref(x_31);
x_33 = l_mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_32);
lean_dec_ref(x_32);
x_34 = l_panic___redArg(x_17, x_33);
x_35 = lean_apply_1(x_34, x_16);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_5 = x_36;
x_6 = x_37;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_1(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_4 = x_12;
x_5 = x_13;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_box(0);
x_4 = x_15;
x_5 = x_14;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Monitor_spinnerFrames;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" [", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Running ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (+ ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" more)", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 5);
if (x_10 == 0)
{
lean_dec_ref(x_3);
goto block_9;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
if (x_11 == 0)
{
lean_dec_ref(x_3);
goto block_9;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_39; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_3);
x_18 = l_Lake_Monitor_print___closed__0;
x_19 = l_Lake_Monitor_spinnerFrames;
x_20 = l_Lake_Monitor_renderProgress___redArg___closed__0;
x_21 = lean_array_fget(x_19, x_16);
x_22 = lean_unbox_uint32(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Fin_add(x_20, x_16, x_23);
lean_dec(x_16);
x_25 = l_Lake_Ansi_resetLine___closed__0;
lean_inc(x_14);
lean_inc(x_13);
lean_ctor_set(x_4, 5, x_24);
lean_ctor_set(x_4, 3, x_25);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get_size(x_1);
x_84 = lean_nat_dec_lt(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
x_85 = lean_array_get_size(x_2);
x_86 = lean_nat_sub(x_85, x_23);
lean_dec(x_85);
x_87 = lean_array_fget(x_2, x_86);
lean_dec(x_86);
x_88 = lean_ctor_get(x_87, 2);
lean_inc_ref(x_88);
lean_dec_ref(x_87);
x_89 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_90 = lean_string_append(x_89, x_88);
lean_dec_ref(x_88);
x_39 = x_90;
goto block_81;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_nat_sub(x_83, x_23);
lean_dec(x_83);
x_92 = lean_array_fget(x_1, x_91);
x_93 = lean_ctor_get(x_92, 2);
lean_inc_ref(x_93);
lean_dec_ref(x_92);
x_94 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_95 = lean_string_append(x_94, x_93);
lean_dec_ref(x_93);
x_96 = l_Lake_Monitor_renderProgress___redArg___closed__5;
x_97 = lean_string_append(x_95, x_96);
x_98 = l_Nat_reprFast(x_91);
x_99 = lean_string_append(x_97, x_98);
lean_dec_ref(x_98);
x_100 = l_Lake_Monitor_renderProgress___redArg___closed__6;
x_101 = lean_string_append(x_99, x_100);
x_39 = x_101;
goto block_81;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
block_38:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_17);
x_33 = lean_apply_1(x_32, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_26 = x_34;
x_27 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_box(0);
x_26 = x_37;
x_27 = x_36;
goto block_30;
}
}
block_81:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_40);
x_41 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_42 = lean_string_push(x_41, x_22);
x_43 = lean_string_append(x_15, x_42);
lean_dec_ref(x_42);
x_44 = l_Lake_Monitor_renderProgress___redArg___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_Nat_reprFast(x_13);
x_47 = lean_string_append(x_45, x_46);
lean_dec_ref(x_46);
x_48 = l_Lake_Monitor_renderProgress___redArg___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_reprFast(x_14);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = l_Lake_print_x21___closed__9;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_39);
lean_dec_ref(x_39);
lean_inc_ref(x_54);
x_55 = lean_apply_2(x_40, x_54, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_31 = x_56;
goto block_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec_ref(x_55);
x_59 = l_Lake_print_x21___closed__2;
x_60 = l_Lake_print_x21___closed__3;
x_61 = lean_unsigned_to_nat(79u);
x_62 = lean_unsigned_to_nat(4u);
x_63 = l_Lake_print_x21___closed__4;
x_64 = l_Lake_print_x21___closed__7;
x_65 = l_Lean_Name_toString(x_64, x_11, x_18);
x_66 = lean_string_append(x_63, x_65);
lean_dec_ref(x_65);
x_67 = l_Lake_print_x21___closed__8;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_io_error_to_string(x_57);
x_70 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_71 = lean_string_append(x_70, x_52);
x_72 = l_String_quote(x_54);
lean_dec_ref(x_54);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_unsigned_to_nat(120u);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_format_pretty(x_73, x_74, x_75, x_75);
x_77 = lean_string_append(x_71, x_76);
lean_dec_ref(x_76);
x_78 = l_mkPanicMessageWithDecl(x_59, x_60, x_61, x_62, x_77);
lean_dec_ref(x_77);
x_79 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_78, x_58);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_31 = x_80;
goto block_38;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint32_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_123; lean_object* x_131; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_102 = lean_ctor_get(x_4, 0);
x_103 = lean_ctor_get(x_4, 1);
x_104 = lean_ctor_get(x_4, 2);
x_105 = lean_ctor_get(x_4, 3);
x_106 = lean_ctor_get(x_4, 4);
x_107 = lean_ctor_get(x_4, 5);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_4);
x_108 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_108);
lean_dec_ref(x_3);
x_109 = l_Lake_Monitor_print___closed__0;
x_110 = l_Lake_Monitor_spinnerFrames;
x_111 = l_Lake_Monitor_renderProgress___redArg___closed__0;
x_112 = lean_array_fget(x_110, x_107);
x_113 = lean_unbox_uint32(x_112);
lean_dec(x_112);
x_114 = lean_unsigned_to_nat(1u);
x_115 = l_Fin_add(x_111, x_107, x_114);
lean_dec(x_107);
x_116 = l_Lake_Ansi_resetLine___closed__0;
lean_inc(x_103);
lean_inc(x_102);
x_117 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_103);
lean_ctor_set(x_117, 2, x_104);
lean_ctor_set(x_117, 3, x_116);
lean_ctor_set(x_117, 4, x_106);
lean_ctor_set(x_117, 5, x_115);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_array_get_size(x_1);
x_176 = lean_nat_dec_lt(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_175);
x_177 = lean_array_get_size(x_2);
x_178 = lean_nat_sub(x_177, x_114);
lean_dec(x_177);
x_179 = lean_array_fget(x_2, x_178);
lean_dec(x_178);
x_180 = lean_ctor_get(x_179, 2);
lean_inc_ref(x_180);
lean_dec_ref(x_179);
x_181 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_182 = lean_string_append(x_181, x_180);
lean_dec_ref(x_180);
x_131 = x_182;
goto block_173;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_183 = lean_nat_sub(x_175, x_114);
lean_dec(x_175);
x_184 = lean_array_fget(x_1, x_183);
x_185 = lean_ctor_get(x_184, 2);
lean_inc_ref(x_185);
lean_dec_ref(x_184);
x_186 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_187 = lean_string_append(x_186, x_185);
lean_dec_ref(x_185);
x_188 = l_Lake_Monitor_renderProgress___redArg___closed__5;
x_189 = lean_string_append(x_187, x_188);
x_190 = l_Nat_reprFast(x_183);
x_191 = lean_string_append(x_189, x_190);
lean_dec_ref(x_190);
x_192 = l_Lake_Monitor_renderProgress___redArg___closed__6;
x_193 = lean_string_append(x_191, x_192);
x_131 = x_193;
goto block_173;
}
block_122:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
block_130:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_124);
lean_dec_ref(x_108);
x_125 = lean_apply_1(x_124, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_118 = x_126;
x_119 = x_127;
goto block_122;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec_ref(x_125);
x_129 = lean_box(0);
x_118 = x_129;
x_119 = x_128;
goto block_122;
}
}
block_173:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_132 = lean_ctor_get(x_108, 4);
lean_inc_ref(x_132);
x_133 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_134 = lean_string_push(x_133, x_113);
x_135 = lean_string_append(x_105, x_134);
lean_dec_ref(x_134);
x_136 = l_Lake_Monitor_renderProgress___redArg___closed__2;
x_137 = lean_string_append(x_135, x_136);
x_138 = l_Nat_reprFast(x_102);
x_139 = lean_string_append(x_137, x_138);
lean_dec_ref(x_138);
x_140 = l_Lake_Monitor_renderProgress___redArg___closed__3;
x_141 = lean_string_append(x_139, x_140);
x_142 = l_Nat_reprFast(x_103);
x_143 = lean_string_append(x_141, x_142);
lean_dec_ref(x_142);
x_144 = l_Lake_print_x21___closed__9;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_131);
lean_dec_ref(x_131);
lean_inc_ref(x_146);
x_147 = lean_apply_2(x_132, x_146, x_5);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
lean_dec_ref(x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec_ref(x_147);
x_123 = x_148;
goto block_130;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec_ref(x_147);
x_151 = l_Lake_print_x21___closed__2;
x_152 = l_Lake_print_x21___closed__3;
x_153 = lean_unsigned_to_nat(79u);
x_154 = lean_unsigned_to_nat(4u);
x_155 = l_Lake_print_x21___closed__4;
x_156 = l_Lake_print_x21___closed__7;
x_157 = l_Lean_Name_toString(x_156, x_11, x_109);
x_158 = lean_string_append(x_155, x_157);
lean_dec_ref(x_157);
x_159 = l_Lake_print_x21___closed__8;
x_160 = lean_string_append(x_158, x_159);
x_161 = lean_io_error_to_string(x_149);
x_162 = lean_string_append(x_160, x_161);
lean_dec_ref(x_161);
x_163 = lean_string_append(x_162, x_144);
x_164 = l_String_quote(x_146);
lean_dec_ref(x_146);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_unsigned_to_nat(120u);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_format_pretty(x_165, x_166, x_167, x_167);
x_169 = lean_string_append(x_163, x_168);
lean_dec_ref(x_168);
x_170 = l_mkPanicMessageWithDecl(x_151, x_152, x_153, x_154, x_169);
lean_dec_ref(x_169);
x_171 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_170, x_150);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec_ref(x_171);
x_123 = x_172;
goto block_130;
}
}
}
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Monitor_renderProgress___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Monitor_renderProgress___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Monitor_renderProgress(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_5, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_11 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_12 = l_Lake_logToStream(x_11, x_1, x_2, x_3, x_9);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_7 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("32", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (Optional)", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; uint32_t x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; uint32_t x_190; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; uint8_t x_232; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_249; uint8_t x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; uint8_t x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_266; lean_object* x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; lean_object* x_271; uint8_t x_277; uint8_t x_278; lean_object* x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_288; lean_object* x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint8_t x_310; uint8_t x_311; lean_object* x_312; uint8_t x_313; uint8_t x_314; uint8_t x_320; lean_object* x_321; uint8_t x_322; uint8_t x_323; lean_object* x_329; lean_object* x_338; lean_object* x_339; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_66 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_338 = lean_task_get_own(x_66);
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec_ref(x_338);
x_329 = x_339;
goto block_337;
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
x_16 = lean_apply_1(x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_5 = x_12;
x_6 = x_17;
x_7 = x_18;
goto block_10;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_box(0);
x_5 = x_12;
x_6 = x_20;
x_7 = x_19;
goto block_10;
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
block_57:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_43);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec_ref(x_43);
lean_dec_ref(x_34);
x_11 = x_42;
x_12 = x_44;
x_13 = x_41;
goto block_21;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec_ref(x_43);
lean_dec_ref(x_34);
x_11 = x_42;
x_12 = x_44;
x_13 = x_41;
goto block_21;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_box(0);
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_53 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_34, x_45, x_39, x_43, x_51, x_52, x_50, x_44, x_41);
lean_dec_ref(x_43);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_11 = x_42;
x_12 = x_56;
x_13 = x_55;
goto block_21;
}
}
}
block_65:
{
if (x_62 == 0)
{
lean_dec_ref(x_60);
lean_dec_ref(x_34);
x_11 = x_59;
x_12 = x_61;
x_13 = x_63;
goto block_21;
}
else
{
if (x_58 == 0)
{
x_41 = x_63;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_35;
goto block_57;
}
else
{
uint8_t x_64; 
x_64 = 0;
x_41 = x_63;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_64;
goto block_57;
}
}
}
block_139:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_77);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_69, 3);
x_80 = lean_ctor_get(x_77, 4);
lean_inc_ref(x_80);
lean_dec_ref(x_77);
lean_ctor_set(x_69, 3, x_73);
x_81 = lean_string_append(x_79, x_76);
lean_dec_ref(x_76);
x_82 = l_Lake_Monitor_reportJob___closed__0;
x_83 = lean_string_append(x_81, x_82);
lean_inc_ref(x_83);
x_84 = lean_apply_2(x_80, x_83, x_75);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = x_69;
x_62 = x_74;
x_63 = x_85;
goto block_65;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = l_Lake_print_x21___closed__2;
x_89 = l_Lake_print_x21___closed__3;
x_90 = lean_unsigned_to_nat(79u);
x_91 = lean_unsigned_to_nat(4u);
x_92 = l_Lake_Monitor_print___closed__3;
x_93 = lean_io_error_to_string(x_86);
x_94 = lean_string_append(x_92, x_93);
lean_dec_ref(x_93);
x_95 = l_Lake_print_x21___closed__9;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_String_quote(x_83);
lean_dec_ref(x_83);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_unsigned_to_nat(120u);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_format_pretty(x_98, x_99, x_100, x_100);
x_102 = lean_string_append(x_96, x_101);
lean_dec_ref(x_101);
x_103 = l_mkPanicMessageWithDecl(x_88, x_89, x_90, x_91, x_102);
lean_dec_ref(x_102);
x_104 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_103, x_87);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec_ref(x_104);
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = x_69;
x_62 = x_74;
x_63 = x_105;
goto block_65;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_106 = lean_ctor_get(x_69, 0);
x_107 = lean_ctor_get(x_69, 1);
x_108 = lean_ctor_get(x_69, 2);
x_109 = lean_ctor_get(x_69, 3);
x_110 = lean_ctor_get(x_69, 4);
x_111 = lean_ctor_get(x_69, 5);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_69);
x_112 = lean_ctor_get(x_77, 4);
lean_inc_ref(x_112);
lean_dec_ref(x_77);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_107);
lean_ctor_set(x_113, 2, x_108);
lean_ctor_set(x_113, 3, x_73);
lean_ctor_set(x_113, 4, x_110);
lean_ctor_set(x_113, 5, x_111);
x_114 = lean_string_append(x_109, x_76);
lean_dec_ref(x_76);
x_115 = l_Lake_Monitor_reportJob___closed__0;
x_116 = lean_string_append(x_114, x_115);
lean_inc_ref(x_116);
x_117 = lean_apply_2(x_112, x_116, x_75);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
lean_dec_ref(x_116);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = x_113;
x_62 = x_74;
x_63 = x_118;
goto block_65;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec_ref(x_117);
x_121 = l_Lake_print_x21___closed__2;
x_122 = l_Lake_print_x21___closed__3;
x_123 = lean_unsigned_to_nat(79u);
x_124 = lean_unsigned_to_nat(4u);
x_125 = l_Lake_Monitor_print___closed__3;
x_126 = lean_io_error_to_string(x_119);
x_127 = lean_string_append(x_125, x_126);
lean_dec_ref(x_126);
x_128 = l_Lake_print_x21___closed__9;
x_129 = lean_string_append(x_127, x_128);
x_130 = l_String_quote(x_116);
lean_dec_ref(x_116);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_unsigned_to_nat(120u);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_format_pretty(x_131, x_132, x_133, x_133);
x_135 = lean_string_append(x_129, x_134);
lean_dec_ref(x_134);
x_136 = l_mkPanicMessageWithDecl(x_121, x_122, x_123, x_124, x_135);
lean_dec_ref(x_135);
x_137 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_136, x_120);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec_ref(x_137);
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = x_113;
x_62 = x_74;
x_63 = x_138;
goto block_65;
}
}
}
block_150:
{
lean_object* x_149; 
x_149 = l_Lake_Ansi_chalk(x_148, x_142);
lean_dec_ref(x_142);
lean_dec_ref(x_148);
x_69 = x_140;
x_70 = x_141;
x_71 = x_143;
x_72 = x_144;
x_73 = x_145;
x_74 = x_146;
x_75 = x_147;
x_76 = x_149;
goto block_139;
}
block_181:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_161 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_162 = lean_string_push(x_161, x_157);
x_163 = l_Lake_Monitor_renderProgress___redArg___closed__2;
x_164 = lean_string_append(x_162, x_163);
x_165 = l_Nat_reprFast(x_28);
x_166 = lean_string_append(x_164, x_165);
lean_dec_ref(x_165);
x_167 = l_Lake_Monitor_renderProgress___redArg___closed__3;
x_168 = lean_string_append(x_166, x_167);
x_169 = l_Nat_reprFast(x_29);
x_170 = lean_string_append(x_168, x_169);
lean_dec_ref(x_169);
x_171 = l_Lake_Monitor_reportJob___closed__1;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_string_append(x_172, x_160);
lean_dec_ref(x_160);
x_174 = l_Lake_Monitor_reportJob___closed__2;
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_string_append(x_175, x_151);
lean_dec_ref(x_151);
x_177 = lean_string_append(x_176, x_174);
x_178 = lean_string_append(x_177, x_67);
lean_dec_ref(x_67);
if (x_39 == 0)
{
x_69 = x_152;
x_70 = x_153;
x_71 = x_155;
x_72 = x_156;
x_73 = x_161;
x_74 = x_158;
x_75 = x_159;
x_76 = x_178;
goto block_139;
}
else
{
if (x_158 == 0)
{
lean_object* x_179; 
x_179 = l_Lake_Monitor_reportJob___closed__3;
x_140 = x_152;
x_141 = x_153;
x_142 = x_178;
x_143 = x_155;
x_144 = x_156;
x_145 = x_161;
x_146 = x_158;
x_147 = x_159;
x_148 = x_179;
goto block_150;
}
else
{
lean_object* x_180; 
x_180 = l_Lake_LogLevel_ansiColor(x_154);
x_140 = x_152;
x_141 = x_153;
x_142 = x_178;
x_143 = x_155;
x_144 = x_156;
x_145 = x_161;
x_146 = x_158;
x_147 = x_159;
x_148 = x_180;
goto block_150;
}
}
}
block_193:
{
if (x_68 == 0)
{
lean_object* x_191; 
x_191 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_151 = x_182;
x_152 = x_183;
x_153 = x_184;
x_154 = x_186;
x_155 = x_185;
x_156 = x_187;
x_157 = x_190;
x_158 = x_188;
x_159 = x_189;
x_160 = x_191;
goto block_181;
}
else
{
lean_object* x_192; 
x_192 = l_Lake_Monitor_reportJob___closed__4;
x_151 = x_182;
x_152 = x_183;
x_153 = x_184;
x_154 = x_186;
x_155 = x_185;
x_156 = x_187;
x_157 = x_190;
x_158 = x_188;
x_159 = x_189;
x_160 = x_192;
goto block_181;
}
}
block_203:
{
uint32_t x_202; 
x_202 = l_Lake_LogLevel_icon(x_197);
x_182 = x_194;
x_183 = x_195;
x_184 = x_196;
x_185 = x_198;
x_186 = x_197;
x_187 = x_199;
x_188 = x_201;
x_189 = x_200;
x_190 = x_202;
goto block_193;
}
block_213:
{
uint8_t x_211; uint32_t x_212; 
x_211 = 0;
x_212 = 10004;
x_182 = x_204;
x_183 = x_205;
x_184 = x_206;
x_185 = x_207;
x_186 = x_208;
x_187 = x_209;
x_188 = x_211;
x_189 = x_210;
x_190 = x_212;
goto block_193;
}
block_224:
{
lean_object* x_223; 
x_223 = l_Lake_JobAction_verb(x_222, x_219);
if (x_222 == 0)
{
if (x_215 == 0)
{
x_204 = x_223;
x_205 = x_214;
x_206 = x_222;
x_207 = x_216;
x_208 = x_217;
x_209 = x_218;
x_210 = x_221;
goto block_213;
}
else
{
if (x_220 == 0)
{
x_204 = x_223;
x_205 = x_214;
x_206 = x_222;
x_207 = x_216;
x_208 = x_217;
x_209 = x_218;
x_210 = x_221;
goto block_213;
}
else
{
x_194 = x_223;
x_195 = x_214;
x_196 = x_222;
x_197 = x_217;
x_198 = x_216;
x_199 = x_218;
x_200 = x_221;
x_201 = x_220;
goto block_203;
}
}
}
else
{
x_194 = x_223;
x_195 = x_214;
x_196 = x_222;
x_197 = x_217;
x_198 = x_216;
x_199 = x_218;
x_200 = x_221;
x_201 = x_222;
goto block_203;
}
}
block_237:
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; uint8_t x_236; 
x_233 = lean_array_get_size(x_228);
x_234 = lean_unsigned_to_nat(0u);
x_235 = lean_nat_dec_eq(x_233, x_234);
lean_dec(x_233);
x_236 = l_instDecidableNot___redArg(x_235);
if (x_236 == 0)
{
x_214 = x_225;
x_215 = x_236;
x_216 = x_227;
x_217 = x_226;
x_218 = x_228;
x_219 = x_229;
x_220 = x_232;
x_221 = x_231;
x_222 = x_236;
goto block_224;
}
else
{
x_214 = x_225;
x_215 = x_236;
x_216 = x_227;
x_217 = x_226;
x_218 = x_228;
x_219 = x_229;
x_220 = x_232;
x_221 = x_231;
x_222 = x_230;
goto block_224;
}
}
block_248:
{
if (x_40 == 0)
{
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_67);
lean_dec_ref(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_22 = x_238;
x_23 = x_246;
goto block_27;
}
else
{
uint8_t x_247; 
x_247 = l_instDecidableNot___redArg(x_39);
if (x_247 == 0)
{
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_67);
lean_dec_ref(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_22 = x_238;
x_23 = x_246;
goto block_27;
}
else
{
if (x_242 == 0)
{
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_67);
lean_dec_ref(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_22 = x_238;
x_23 = x_246;
goto block_27;
}
else
{
x_225 = x_238;
x_226 = x_240;
x_227 = x_239;
x_228 = x_241;
x_229 = x_243;
x_230 = x_244;
x_231 = x_246;
x_232 = x_245;
goto block_237;
}
}
}
}
block_262:
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_261; 
x_258 = lean_array_get_size(x_253);
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_nat_dec_eq(x_258, x_259);
lean_dec(x_258);
x_261 = l_instDecidableNot___redArg(x_260);
if (x_261 == 0)
{
x_238 = x_249;
x_239 = x_251;
x_240 = x_250;
x_241 = x_253;
x_242 = x_252;
x_243 = x_254;
x_244 = x_255;
x_245 = x_257;
x_246 = x_256;
goto block_248;
}
else
{
if (x_257 == 0)
{
x_238 = x_249;
x_239 = x_251;
x_240 = x_250;
x_241 = x_253;
x_242 = x_252;
x_243 = x_254;
x_244 = x_255;
x_245 = x_257;
x_246 = x_256;
goto block_248;
}
else
{
x_225 = x_249;
x_226 = x_250;
x_227 = x_251;
x_228 = x_253;
x_229 = x_254;
x_230 = x_255;
x_231 = x_256;
x_232 = x_257;
goto block_237;
}
}
}
block_276:
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_275; 
x_272 = lean_array_get_size(x_267);
x_273 = lean_unsigned_to_nat(0u);
x_274 = lean_nat_dec_eq(x_272, x_273);
lean_dec(x_272);
x_275 = l_instDecidableNot___redArg(x_274);
if (x_275 == 0)
{
x_249 = x_263;
x_250 = x_265;
x_251 = x_264;
x_252 = x_266;
x_253 = x_267;
x_254 = x_268;
x_255 = x_269;
x_256 = x_271;
x_257 = x_270;
goto block_262;
}
else
{
if (x_269 == 0)
{
x_249 = x_263;
x_250 = x_265;
x_251 = x_264;
x_252 = x_266;
x_253 = x_267;
x_254 = x_268;
x_255 = x_269;
x_256 = x_271;
x_257 = x_270;
goto block_262;
}
else
{
x_225 = x_263;
x_226 = x_265;
x_227 = x_264;
x_228 = x_267;
x_229 = x_268;
x_230 = x_269;
x_231 = x_271;
x_232 = x_270;
goto block_237;
}
}
}
block_287:
{
uint8_t x_286; 
x_286 = l_instDecidableNot___redArg(x_68);
if (x_286 == 0)
{
if (x_38 == 0)
{
lean_dec_ref(x_283);
lean_dec_ref(x_279);
lean_dec_ref(x_67);
lean_dec_ref(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_22 = x_284;
x_23 = x_285;
goto block_27;
}
else
{
x_263 = x_284;
x_264 = x_283;
x_265 = x_277;
x_266 = x_278;
x_267 = x_279;
x_268 = x_280;
x_269 = x_281;
x_270 = x_282;
x_271 = x_285;
goto block_276;
}
}
else
{
x_263 = x_284;
x_264 = x_283;
x_265 = x_277;
x_266 = x_278;
x_267 = x_279;
x_268 = x_280;
x_269 = x_281;
x_270 = x_282;
x_271 = x_285;
goto block_276;
}
}
block_309:
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; 
x_294 = lean_array_get_size(x_289);
x_295 = lean_unsigned_to_nat(0u);
x_296 = lean_nat_dec_eq(x_294, x_295);
lean_dec(x_294);
x_297 = l_instDecidableNot___redArg(x_296);
if (x_297 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_277 = x_288;
x_278 = x_290;
x_279 = x_289;
x_280 = x_291;
x_281 = x_293;
x_282 = x_292;
x_283 = x_2;
x_284 = x_3;
x_285 = x_4;
goto block_287;
}
else
{
if (x_293 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_277 = x_288;
x_278 = x_290;
x_279 = x_289;
x_280 = x_291;
x_281 = x_293;
x_282 = x_292;
x_283 = x_2;
x_284 = x_3;
x_285 = x_4;
goto block_287;
}
else
{
uint8_t x_298; 
x_298 = l_instDecidableNot___redArg(x_68);
if (x_298 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
x_277 = x_288;
x_278 = x_290;
x_279 = x_289;
x_280 = x_291;
x_281 = x_293;
x_282 = x_292;
x_283 = x_2;
x_284 = x_3;
x_285 = x_4;
goto block_287;
}
else
{
uint8_t x_299; 
x_299 = !lean_is_exclusive(x_3);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_300 = lean_ctor_get(x_3, 5);
lean_dec(x_300);
x_301 = lean_ctor_get(x_3, 4);
lean_dec(x_301);
x_302 = lean_ctor_get(x_3, 3);
lean_dec(x_302);
x_303 = lean_ctor_get(x_3, 2);
lean_dec(x_303);
x_304 = lean_ctor_get(x_3, 1);
lean_dec(x_304);
x_305 = lean_ctor_get(x_3, 0);
lean_dec(x_305);
lean_inc_ref(x_67);
x_306 = lean_array_push(x_30, x_67);
lean_inc(x_29);
lean_inc(x_28);
lean_ctor_set(x_3, 2, x_306);
x_277 = x_288;
x_278 = x_290;
x_279 = x_289;
x_280 = x_291;
x_281 = x_293;
x_282 = x_292;
x_283 = x_2;
x_284 = x_3;
x_285 = x_4;
goto block_287;
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_3);
lean_inc_ref(x_67);
x_307 = lean_array_push(x_30, x_67);
lean_inc(x_29);
lean_inc(x_28);
x_308 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_308, 0, x_28);
lean_ctor_set(x_308, 1, x_29);
lean_ctor_set(x_308, 2, x_307);
lean_ctor_set(x_308, 3, x_31);
lean_ctor_set(x_308, 4, x_32);
lean_ctor_set(x_308, 5, x_33);
x_277 = x_288;
x_278 = x_290;
x_279 = x_289;
x_280 = x_291;
x_281 = x_293;
x_282 = x_292;
x_283 = x_2;
x_284 = x_308;
x_285 = x_4;
goto block_287;
}
}
}
}
}
block_319:
{
uint8_t x_315; lean_object* x_316; 
x_315 = l_Lake_ordLogLevel____x40_Lake_Util_Log___hyg_760_(x_36, x_310);
x_316 = lean_box(x_315);
if (lean_obj_tag(x_316) == 2)
{
uint8_t x_317; 
x_317 = 0;
x_288 = x_310;
x_289 = x_312;
x_290 = x_311;
x_291 = x_313;
x_292 = x_314;
x_293 = x_317;
goto block_309;
}
else
{
uint8_t x_318; 
lean_dec(x_316);
x_318 = 1;
x_288 = x_310;
x_289 = x_312;
x_290 = x_311;
x_291 = x_313;
x_292 = x_314;
x_293 = x_318;
goto block_309;
}
}
block_328:
{
uint8_t x_324; lean_object* x_325; 
x_324 = l_Lake_ordLogLevel____x40_Lake_Util_Log___hyg_760_(x_35, x_320);
x_325 = lean_box(x_324);
if (lean_obj_tag(x_325) == 2)
{
uint8_t x_326; 
x_326 = 0;
x_310 = x_320;
x_311 = x_323;
x_312 = x_321;
x_313 = x_322;
x_314 = x_326;
goto block_319;
}
else
{
uint8_t x_327; 
lean_dec(x_325);
x_327 = 1;
x_310 = x_320;
x_311 = x_323;
x_312 = x_321;
x_313 = x_322;
x_314 = x_327;
goto block_319;
}
}
block_337:
{
lean_object* x_330; uint8_t x_331; uint8_t x_332; uint8_t x_333; lean_object* x_334; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc_ref(x_330);
x_331 = lean_ctor_get_uint8(x_329, sizeof(void*)*2);
lean_dec_ref(x_329);
x_332 = l_Lake_Log_maxLv(x_330);
x_333 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_266_(x_37, x_331);
x_334 = lean_box(x_333);
if (lean_obj_tag(x_334) == 2)
{
uint8_t x_335; 
x_335 = 0;
x_320 = x_332;
x_321 = x_330;
x_322 = x_331;
x_323 = x_335;
goto block_328;
}
else
{
uint8_t x_336; 
lean_dec(x_334);
x_336 = 1;
x_320 = x_332;
x_321 = x_330;
x_322 = x_331;
x_323 = x_336;
goto block_328;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_1, x_10, x_11, x_4, x_12, x_13, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_array_uget(x_1, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_io_get_task_state(x_19, x_7);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
switch (x_22) {
case 0:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_4, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec_ref(x_20);
x_27 = lean_array_push(x_17, x_18);
lean_ctor_set(x_4, 1, x_27);
x_8 = x_4;
x_9 = x_6;
x_10 = x_26;
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec_ref(x_20);
x_29 = lean_array_push(x_17, x_18);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
x_8 = x_30;
x_9 = x_6;
x_10 = x_28;
goto block_14;
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_4, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec_ref(x_20);
lean_inc_ref(x_18);
x_35 = lean_array_push(x_16, x_18);
x_36 = lean_array_push(x_17, x_18);
lean_ctor_set(x_4, 1, x_36);
lean_ctor_set(x_4, 0, x_35);
x_8 = x_4;
x_9 = x_6;
x_10 = x_34;
goto block_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_dec_ref(x_20);
lean_inc_ref(x_18);
x_38 = lean_array_push(x_16, x_18);
x_39 = lean_array_push(x_17, x_18);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_8 = x_40;
x_9 = x_6;
x_10 = x_37;
goto block_14;
}
}
default: 
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_16);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec_ref(x_20);
lean_inc_ref(x_5);
x_42 = l_Lake_Monitor_reportJob(x_18, x_5, x_6, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec_ref(x_42);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_49);
x_8 = x_4;
x_9 = x_44;
x_10 = x_45;
goto block_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
x_52 = lean_ctor_get(x_44, 2);
x_53 = lean_ctor_get(x_44, 3);
x_54 = lean_ctor_get(x_44, 4);
x_55 = lean_ctor_get(x_44, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_50, x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
x_8 = x_4;
x_9 = x_58;
x_10 = x_45;
goto block_14;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_6);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_7);
return x_60;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_8;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Monitor_poll___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkBuildContext___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_poll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lake_mkBuildContext___closed__0;
x_12 = lean_st_ref_set(x_5, x_11, x_9);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_array_get_size(x_8);
x_29 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_29);
x_30 = l_Lake_Monitor_poll___closed__0;
x_31 = lean_array_get_size(x_1);
x_32 = lean_nat_dec_lt(x_10, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_inc_ref(x_3);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_30);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_6);
x_19 = x_12;
x_20 = x_30;
x_21 = x_3;
x_22 = x_14;
goto block_28;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_inc_ref(x_3);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_30);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_6);
x_19 = x_12;
x_20 = x_30;
x_21 = x_3;
x_22 = x_14;
goto block_28;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_12);
lean_free_object(x_6);
x_34 = 0;
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
lean_inc_ref(x_2);
x_36 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_34, x_35, x_30, x_2, x_3, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_19 = x_36;
x_20 = x_39;
x_21 = x_40;
x_22 = x_38;
goto block_28;
}
}
block_28:
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_10, x_18);
if (x_23 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_19;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_18, x_18);
if (x_24 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_19;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec_ref(x_19);
x_25 = 0;
x_26 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_27 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_8, x_25, x_26, x_20, x_2, x_21, x_22);
lean_dec(x_8);
return x_27;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_ctor_get(x_3, 3);
x_45 = lean_ctor_get(x_3, 4);
x_46 = lean_ctor_get(x_3, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_3);
x_47 = lean_array_get_size(x_8);
x_58 = lean_nat_add(x_42, x_47);
lean_dec(x_42);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_43);
lean_ctor_set(x_59, 3, x_44);
lean_ctor_set(x_59, 4, x_45);
lean_ctor_set(x_59, 5, x_46);
x_60 = l_Lake_Monitor_poll___closed__0;
x_61 = lean_array_get_size(x_1);
x_62 = lean_nat_dec_lt(x_10, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_inc_ref(x_59);
lean_ctor_set(x_6, 1, x_59);
lean_ctor_set(x_6, 0, x_60);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_6);
x_48 = x_12;
x_49 = x_60;
x_50 = x_59;
x_51 = x_14;
goto block_57;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_inc_ref(x_59);
lean_ctor_set(x_6, 1, x_59);
lean_ctor_set(x_6, 0, x_60);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_6);
x_48 = x_12;
x_49 = x_60;
x_50 = x_59;
x_51 = x_14;
goto block_57;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_12);
lean_free_object(x_6);
x_64 = 0;
x_65 = lean_usize_of_nat(x_61);
lean_dec(x_61);
lean_inc_ref(x_2);
x_66 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_64, x_65, x_60, x_2, x_59, x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_48 = x_66;
x_49 = x_69;
x_50 = x_70;
x_51 = x_68;
goto block_57;
}
}
block_57:
{
uint8_t x_52; 
x_52 = lean_nat_dec_lt(x_10, x_47);
if (x_52 == 0)
{
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_48;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_47, x_47);
if (x_53 == 0)
{
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_48;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
lean_dec_ref(x_48);
x_54 = 0;
x_55 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_56 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_8, x_54, x_55, x_49, x_2, x_50, x_51);
lean_dec(x_8);
return x_56;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
lean_dec(x_12);
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_3, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 5);
lean_inc(x_77);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_78 = x_3;
} else {
 lean_dec_ref(x_3);
 x_78 = lean_box(0);
}
x_79 = lean_array_get_size(x_8);
x_90 = lean_nat_add(x_73, x_79);
lean_dec(x_73);
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 6, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_74);
lean_ctor_set(x_91, 3, x_75);
lean_ctor_set(x_91, 4, x_76);
lean_ctor_set(x_91, 5, x_77);
x_92 = l_Lake_Monitor_poll___closed__0;
x_93 = lean_array_get_size(x_1);
x_94 = lean_nat_dec_lt(x_10, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_93);
lean_inc_ref(x_91);
lean_ctor_set(x_6, 1, x_91);
lean_ctor_set(x_6, 0, x_92);
lean_inc(x_71);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_6);
lean_ctor_set(x_95, 1, x_71);
x_80 = x_95;
x_81 = x_92;
x_82 = x_91;
x_83 = x_71;
goto block_89;
}
else
{
uint8_t x_96; 
x_96 = lean_nat_dec_le(x_93, x_93);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_93);
lean_inc_ref(x_91);
lean_ctor_set(x_6, 1, x_91);
lean_ctor_set(x_6, 0, x_92);
lean_inc(x_71);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_6);
lean_ctor_set(x_97, 1, x_71);
x_80 = x_97;
x_81 = x_92;
x_82 = x_91;
x_83 = x_71;
goto block_89;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_6);
x_98 = 0;
x_99 = lean_usize_of_nat(x_93);
lean_dec(x_93);
lean_inc_ref(x_2);
x_100 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_98, x_99, x_92, x_2, x_91, x_71);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_80 = x_100;
x_81 = x_103;
x_82 = x_104;
x_83 = x_102;
goto block_89;
}
}
block_89:
{
uint8_t x_84; 
x_84 = lean_nat_dec_lt(x_10, x_79);
if (x_84 == 0)
{
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_79);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_80;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_79, x_79);
if (x_85 == 0)
{
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_79);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_80;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
lean_dec_ref(x_80);
x_86 = 0;
x_87 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_88 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_8, x_86, x_87, x_81, x_2, x_82, x_83);
lean_dec(x_8);
return x_88;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_105 = lean_ctor_get(x_6, 0);
x_106 = lean_ctor_get(x_6, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_6);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lake_mkBuildContext___closed__0;
x_109 = lean_st_ref_set(x_5, x_108, x_106);
lean_dec(x_5);
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
x_112 = lean_ctor_get(x_3, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_3, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_3, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_3, 5);
lean_inc(x_117);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_118 = x_3;
} else {
 lean_dec_ref(x_3);
 x_118 = lean_box(0);
}
x_119 = lean_array_get_size(x_105);
x_130 = lean_nat_add(x_113, x_119);
lean_dec(x_113);
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_112);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_114);
lean_ctor_set(x_131, 3, x_115);
lean_ctor_set(x_131, 4, x_116);
lean_ctor_set(x_131, 5, x_117);
x_132 = l_Lake_Monitor_poll___closed__0;
x_133 = lean_array_get_size(x_1);
x_134 = lean_nat_dec_lt(x_107, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_133);
lean_inc_ref(x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_131);
lean_inc(x_110);
if (lean_is_scalar(x_111)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_111;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_110);
x_120 = x_136;
x_121 = x_132;
x_122 = x_131;
x_123 = x_110;
goto block_129;
}
else
{
uint8_t x_137; 
x_137 = lean_nat_dec_le(x_133, x_133);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_inc_ref(x_131);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_131);
lean_inc(x_110);
if (lean_is_scalar(x_111)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_111;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_110);
x_120 = x_139;
x_121 = x_132;
x_122 = x_131;
x_123 = x_110;
goto block_129;
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_111);
x_140 = 0;
x_141 = lean_usize_of_nat(x_133);
lean_dec(x_133);
lean_inc_ref(x_2);
x_142 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_140, x_141, x_132, x_2, x_131, x_110);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_120 = x_142;
x_121 = x_145;
x_122 = x_146;
x_123 = x_144;
goto block_129;
}
}
block_129:
{
uint8_t x_124; 
x_124 = lean_nat_dec_lt(x_107, x_119);
if (x_124 == 0)
{
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec(x_105);
lean_dec_ref(x_2);
return x_120;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_119, x_119);
if (x_125 == 0)
{
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec(x_119);
lean_dec(x_105);
lean_dec_ref(x_2);
return x_120;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
lean_dec_ref(x_120);
x_126 = 0;
x_127 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_128 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_105, x_126, x_127, x_121, x_2, x_122, x_123);
lean_dec(x_105);
return x_128;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_io_mono_ms_now(x_3);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_2, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
x_40 = lean_nat_sub(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
x_41 = lean_nat_sub(x_39, x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
x_4 = x_2;
x_5 = x_37;
goto block_34;
}
else
{
uint32_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_uint32_of_nat(x_41);
lean_dec(x_41);
x_45 = l_IO_sleep(x_44, x_37);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_4 = x_2;
x_5 = x_46;
goto block_34;
}
block_34:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_mono_ms_now(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_4, 4);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_4, 4, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
x_18 = lean_ctor_get(x_4, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_13);
lean_ctor_set(x_20, 5, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_4, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 6, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Monitor_sleep(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_2);
x_18 = lean_box(0);
lean_ctor_set(x_7, 1, x_11);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_5, 0, x_7);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
lean_free_object(x_5);
lean_inc_ref(x_2);
x_19 = l_Lake_Monitor_renderProgress___redArg(x_13, x_14, x_2, x_11, x_9);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lake_Monitor_sleep(x_2, x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_1 = x_14;
x_3 = x_26;
x_4 = x_25;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_5);
lean_inc_ref(x_2);
x_35 = l_Lake_Monitor_renderProgress___redArg(x_28, x_29, x_2, x_11, x_9);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lake_Monitor_sleep(x_2, x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_1 = x_29;
x_3 = x_42;
x_4 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_48 = x_7;
} else {
 lean_dec_ref(x_7);
 x_48 = lean_box(0);
}
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_47);
x_51 = lean_nat_dec_lt(x_49, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec_ref(x_2);
x_52 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_48);
lean_inc_ref(x_2);
x_55 = l_Lake_Monitor_renderProgress___redArg(x_46, x_47, x_2, x_45, x_44);
lean_dec(x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lake_Monitor_sleep(x_2, x_58, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_1 = x_47;
x_3 = x_62;
x_4 = x_61;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Monitor_main___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_2);
x_5 = l_Lake_Monitor_loop(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_10 = x_5;
} else {
 lean_dec_ref(x_5);
 x_10 = lean_box(0);
}
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lake_Monitor_renderProgress___redArg___closed__1;
lean_ctor_set(x_7, 3, x_13);
x_19 = lean_string_utf8_byte_size(x_12);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_24);
lean_dec_ref(x_22);
lean_inc_ref(x_12);
x_32 = lean_apply_2(x_24, x_12, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_25 = x_33;
goto block_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_box(x_21);
x_37 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lake_print_x21___closed__2;
x_39 = l_Lake_print_x21___closed__3;
x_40 = lean_unsigned_to_nat(79u);
x_41 = lean_unsigned_to_nat(4u);
x_42 = l_Lake_print_x21___closed__4;
x_43 = l_Lake_print_x21___closed__7;
x_44 = 1;
x_45 = l_Lean_Name_toString(x_43, x_44, x_37);
x_46 = lean_string_append(x_42, x_45);
lean_dec_ref(x_45);
x_47 = l_Lake_print_x21___closed__8;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_io_error_to_string(x_34);
x_50 = lean_string_append(x_48, x_49);
lean_dec_ref(x_49);
x_51 = l_Lake_print_x21___closed__9;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_String_quote(x_12);
lean_dec_ref(x_12);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_unsigned_to_nat(120u);
x_56 = lean_format_pretty(x_54, x_55, x_20, x_20);
x_57 = lean_string_append(x_52, x_56);
lean_dec_ref(x_56);
x_58 = l_mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_57);
lean_dec_ref(x_57);
x_59 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_58, x_35);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec_ref(x_59);
x_25 = x_60;
goto block_31;
}
block_31:
{
lean_object* x_26; 
x_26 = lean_apply_1(x_23, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_14 = x_27;
x_15 = x_28;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = lean_box(0);
x_14 = x_30;
x_15 = x_29;
goto block_18;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_9);
return x_63;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
if (lean_is_scalar(x_8)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_8;
}
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
if (lean_is_scalar(x_10)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_10;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
x_66 = lean_ctor_get(x_7, 2);
x_67 = lean_ctor_get(x_7, 3);
x_68 = lean_ctor_get(x_7, 4);
x_69 = lean_ctor_get(x_7, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_7);
x_70 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
x_77 = lean_string_utf8_byte_size(x_67);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_90; 
x_80 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_2);
x_81 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_82);
lean_dec_ref(x_80);
lean_inc_ref(x_67);
x_90 = lean_apply_2(x_82, x_67, x_9);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec_ref(x_67);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_83 = x_91;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec_ref(x_90);
x_94 = lean_box(x_79);
x_95 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_95, 0, x_94);
x_96 = l_Lake_print_x21___closed__2;
x_97 = l_Lake_print_x21___closed__3;
x_98 = lean_unsigned_to_nat(79u);
x_99 = lean_unsigned_to_nat(4u);
x_100 = l_Lake_print_x21___closed__4;
x_101 = l_Lake_print_x21___closed__7;
x_102 = 1;
x_103 = l_Lean_Name_toString(x_101, x_102, x_95);
x_104 = lean_string_append(x_100, x_103);
lean_dec_ref(x_103);
x_105 = l_Lake_print_x21___closed__8;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_io_error_to_string(x_92);
x_108 = lean_string_append(x_106, x_107);
lean_dec_ref(x_107);
x_109 = l_Lake_print_x21___closed__9;
x_110 = lean_string_append(x_108, x_109);
x_111 = l_String_quote(x_67);
lean_dec_ref(x_67);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_unsigned_to_nat(120u);
x_114 = lean_format_pretty(x_112, x_113, x_78, x_78);
x_115 = lean_string_append(x_110, x_114);
lean_dec_ref(x_114);
x_116 = l_mkPanicMessageWithDecl(x_96, x_97, x_98, x_99, x_115);
lean_dec_ref(x_115);
x_117 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_116, x_93);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_83 = x_118;
goto block_89;
}
block_89:
{
lean_object* x_84; 
x_84 = lean_apply_1(x_81, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_72 = x_85;
x_73 = x_86;
goto block_76;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = lean_box(0);
x_72 = x_88;
x_73 = x_87;
goto block_76;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_67);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_71);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_9);
return x_121;
}
block_76:
{
lean_object* x_74; lean_object* x_75; 
if (lean_is_scalar(x_8)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_8;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_71);
if (lean_is_scalar(x_10)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_10;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_main___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_Monitor_main___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_io_mono_ms_now(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_alloc_ctor(0, 3, 6);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 4, x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 5, x_9);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_10);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_18);
x_20 = l_Lake_Monitor_main(x_1, x_17, x_19, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_28);
lean_dec(x_23);
lean_ctor_set(x_21, 1, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_31);
lean_dec(x_23);
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_35 = x_20;
} else {
 lean_dec_ref(x_20);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = lean_unbox(x_7);
x_18 = lean_unbox(x_8);
x_19 = lean_unbox(x_9);
x_20 = l_Lake_monitorJobs(x_1, x_2, x_3, x_14, x_15, x_16, x_17, x_18, x_19, x_10, x_11, x_12, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_2, x_3);
x_17 = lean_ctor_get(x_16, 19);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_16);
x_18 = lean_box(0);
x_8 = x_18;
x_9 = x_6;
x_10 = x_7;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_get(x_19, x_7);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc_ref(x_1);
x_23 = l_Lake_Package_inputsFileIn(x_1, x_16);
x_24 = l_Lake_CacheMap_save(x_23, x_21, x_6, x_22);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec_ref(x_25);
x_8 = x_27;
x_9 = x_28;
x_10 = x_26;
goto block_14;
}
else
{
lean_dec_ref(x_25);
lean_dec_ref(x_1);
return x_24;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_8;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_saveInputs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = l_Lake_Cache_isDisabled(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_5);
x_10 = lean_box(0);
x_11 = lean_nat_dec_lt(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_9, x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(x_6, x_5, x_17, x_18, x_10, x_2, x_3);
lean_dec_ref(x_5);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdout(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdin(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stderr(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec_ref(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_10 = x_39;
x_11 = x_45;
x_12 = x_44;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(131u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
x_19 = lean_st_mk_ref(x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_mk_ref(x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_IO_FS_Stream_ofBuffer(x_20);
lean_inc(x_23);
x_26 = l_IO_FS_Stream_ofBuffer(x_23);
if (x_2 == 0)
{
x_27 = x_1;
goto block_54;
}
else
{
lean_object* x_55; 
lean_inc_ref(x_26);
x_55 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2), 10, 3);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_26);
lean_closure_set(x_55, 2, x_1);
x_27 = x_55;
goto block_54;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
block_54:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0), 10, 3);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_25, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_st_ref_get(x_23, x_31);
lean_dec(x_23);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
x_40 = l_panic___at___IO_FS_withIsolatedStreams___at___Lean_Meta_realizeConst_realizeAndReport_spec__1_spec__3(x_39);
x_10 = x_33;
x_11 = x_32;
x_12 = x_36;
x_13 = x_40;
goto block_17;
}
else
{
lean_object* x_41; 
x_41 = lean_string_from_utf8_unchecked(x_37);
lean_dec_ref(x_37);
x_10 = x_33;
x_11 = x_32;
x_12 = x_36;
x_13 = x_41;
goto block_17;
}
}
else
{
uint8_t x_42; 
lean_dec(x_23);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_29, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_29, 0, x_47);
return x_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_51 = x_30;
} else {
 lean_dec_ref(x_30);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("- ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_4, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_15);
x_16 = lean_array_uget(x_3, x_4);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0;
x_18 = lean_string_append(x_17, x_16);
lean_dec_ref(x_16);
x_19 = l_Lake_Monitor_reportJob___closed__0;
x_20 = lean_string_append(x_18, x_19);
lean_inc_ref(x_20);
x_21 = lean_apply_2(x_15, x_20, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_8 = x_22;
x_9 = x_23;
goto block_13;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = l_Lake_print_x21___closed__2;
x_27 = l_Lake_print_x21___closed__3;
x_28 = lean_unsigned_to_nat(79u);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lake_print_x21___closed__4;
x_31 = l_Lake_print_x21___closed__7;
x_32 = 1;
lean_inc_ref(x_2);
x_33 = l_Lean_Name_toString(x_31, x_32, x_2);
x_34 = lean_string_append(x_30, x_33);
lean_dec_ref(x_33);
x_35 = l_Lake_print_x21___closed__8;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_io_error_to_string(x_24);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = l_Lake_print_x21___closed__9;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_String_quote(x_20);
lean_dec_ref(x_20);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_unsigned_to_nat(120u);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_format_pretty(x_42, x_43, x_44, x_44);
x_46 = lean_string_append(x_40, x_45);
lean_dec_ref(x_45);
x_47 = l_mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_46);
lean_dec_ref(x_46);
x_48 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_47, x_25);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_8 = x_49;
x_9 = x_50;
goto block_13;
}
}
else
{
lean_object* x_51; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_7);
return x_51;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_4, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_15);
x_16 = lean_array_uget(x_3, x_4);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0;
x_18 = lean_string_append(x_17, x_16);
lean_dec_ref(x_16);
x_19 = l_Lake_Monitor_reportJob___closed__0;
x_20 = lean_string_append(x_18, x_19);
lean_inc_ref(x_20);
x_21 = lean_apply_2(x_15, x_20, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_8 = x_22;
x_9 = x_23;
goto block_13;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = l_Lake_print_x21___closed__2;
x_27 = l_Lake_print_x21___closed__3;
x_28 = lean_unsigned_to_nat(79u);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lake_print_x21___closed__4;
x_31 = l_Lake_print_x21___closed__7;
x_32 = 1;
lean_inc_ref(x_2);
x_33 = l_Lean_Name_toString(x_31, x_32, x_2);
x_34 = lean_string_append(x_30, x_33);
lean_dec_ref(x_33);
x_35 = l_Lake_print_x21___closed__8;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_io_error_to_string(x_24);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = l_Lake_print_x21___closed__9;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_String_quote(x_20);
lean_dec_ref(x_20);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_unsigned_to_nat(120u);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_format_pretty(x_42, x_43, x_44, x_44);
x_46 = lean_string_append(x_40, x_45);
lean_dec_ref(x_45);
x_47 = l_mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_46);
lean_dec_ref(x_46);
x_48 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_47, x_25);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_8 = x_49;
x_9 = x_50;
goto block_13;
}
}
else
{
lean_object* x_51; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_7);
return x_51;
}
block_13:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(x_1, x_2, x_3, x_11, x_5, x_8, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_10 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_2, x_3, x_8);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_7 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_recFetch___at___Lake_recFetchAcyclic___at___Lake_recFetchWithIndex_spec__0_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_7, 0, x_16);
lean_ctor_set(x_12, 1, x_7);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_23 = x_12;
} else {
 lean_dec_ref(x_12);
 x_23 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_22);
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_7, 0, x_29);
lean_ctor_set(x_12, 1, x_7);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_11, 0, x_32);
return x_11;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_36 = x_12;
} else {
 lean_dec_ref(x_12);
 x_36 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_35);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_39);
lean_dec(x_7);
x_42 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_39, x_8);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_53 = x_42;
} else {
 lean_dec_ref(x_42);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_25 = lean_string_utf8_byte_size(x_18);
x_26 = lean_nat_dec_eq(x_25, x_9);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(x_18, x_30, x_25);
x_32 = lean_string_utf8_extract(x_18, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_18);
x_33 = lean_string_append(x_29, x_32);
lean_dec_ref(x_32);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_push(x_28, x_35);
lean_ctor_set(x_16, 0, x_36);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_16);
x_40 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
x_41 = l_Substring_takeWhileAux___at___Lean_PrettyPrinter_Formatter_pushToken_spec__0(x_18, x_25, x_9);
x_42 = l_Substring_takeRightWhileAux___at___Lean_Parser_Term_Doc_getRecommendedSpellingString_bullet_spec__0(x_18, x_41, x_25);
x_43 = lean_string_utf8_extract(x_18, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_18);
x_44 = lean_string_append(x_40, x_43);
lean_dec_ref(x_43);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_push(x_37, x_46);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_38);
x_20 = x_48;
x_21 = x_14;
goto block_24;
}
}
else
{
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_9);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_15;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_11, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_11, 0, x_54);
return x_11;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_dec(x_11);
x_56 = lean_ctor_get(x_12, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_58 = x_12;
} else {
 lean_dec_ref(x_12);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__3;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__4;
x_2 = 0;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Build completed successfully (", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(").\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" jobs", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1 job", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Some required builds logged failures:\n", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__10;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(120u);
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__12;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("top-level build failed", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__14;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("job computation", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("There were issues saving input mappings to the local artifact cache:\n", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__18;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(120u);
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__20;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to save input mappings to the local artifact cache.\n", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__22;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(120u);
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__24;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_183; uint8_t x_184; lean_object* x_185; uint8_t x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_203; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 7);
x_15 = l_Lake_OutStream_get(x_12, x_4);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_16);
x_23 = l_Lake_AnsiMode_isEnabled(x_16, x_13, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_26 = l_Lake_mkBuildContext(x_1, x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_box(1);
x_30 = lean_st_mk_ref(x_29, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__0), 7, 0);
x_34 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__1), 8, 1);
lean_closure_set(x_34, 0, x_2);
x_35 = lean_unsigned_to_nat(0u);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = l_Lake_Workspace_runFetchM___redArg___closed__2;
x_55 = 0;
x_56 = l_Lake_Workspace_runFetchM___redArg___closed__5;
x_57 = 1;
x_58 = lean_box(x_57);
lean_inc(x_27);
lean_inc(x_31);
x_59 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__2___boxed), 10, 9);
lean_closure_set(x_59, 0, x_34);
lean_closure_set(x_59, 1, x_58);
lean_closure_set(x_59, 2, x_33);
lean_closure_set(x_59, 3, x_53);
lean_closure_set(x_59, 4, x_52);
lean_closure_set(x_59, 5, x_31);
lean_closure_set(x_59, 6, x_27);
lean_closure_set(x_59, 7, x_56);
lean_closure_set(x_59, 8, x_35);
x_60 = lean_io_as_task(x_59, x_35, x_32);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_st_ref_get(x_31, x_62);
lean_dec(x_31);
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
x_66 = l_Lake_Monitor_print___closed__0;
x_121 = lean_box(0);
x_122 = l_Lake_BuildConfig_showProgress(x_3);
lean_dec_ref(x_3);
x_183 = l_Lake_Workspace_runFetchM___redArg___closed__16;
x_184 = 0;
lean_inc(x_61);
x_185 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_185, 0, x_61);
lean_ctor_set(x_185, 1, x_121);
lean_ctor_set(x_185, 2, x_183);
lean_ctor_set_uint8(x_185, sizeof(void*)*3, x_184);
x_186 = 2;
x_187 = l_Lake_instDecidableEqVerbosity(x_9, x_186);
if (x_187 == 0)
{
uint8_t x_271; 
x_271 = 2;
x_203 = x_271;
goto block_270;
}
else
{
x_203 = x_55;
goto block_270;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_19);
lean_dec(x_16);
x_20 = lean_apply_1(x_19, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_5 = x_21;
goto block_8;
}
block_51:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_array_get_size(x_37);
x_40 = lean_nat_dec_lt(x_35, x_39);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
x_18 = x_38;
goto block_22;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_39, x_39);
if (x_41 == 0)
{
lean_dec(x_39);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
x_18 = x_38;
goto block_22;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_42 = lean_box(0);
x_43 = 0;
x_44 = lean_usize_of_nat(x_39);
lean_dec(x_39);
lean_inc(x_16);
x_45 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(x_16, x_36, x_37, x_43, x_44, x_42, x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_18 = x_46;
goto block_22;
}
else
{
uint8_t x_47; 
lean_dec(x_16);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
block_108:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_71);
lean_dec(x_16);
x_72 = l_Lake_Workspace_runFetchM___redArg___closed__6;
x_73 = lean_string_append(x_72, x_70);
lean_dec_ref(x_70);
x_74 = l_Lake_Workspace_runFetchM___redArg___closed__7;
x_75 = lean_string_append(x_73, x_74);
lean_inc_ref(x_75);
x_76 = lean_apply_2(x_71, x_75, x_69);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec_ref(x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_67);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_67);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec_ref(x_76);
x_83 = l_Lake_print_x21___closed__2;
x_84 = l_Lake_print_x21___closed__3;
x_85 = lean_unsigned_to_nat(79u);
x_86 = lean_unsigned_to_nat(4u);
x_87 = l_Lake_print_x21___closed__4;
x_88 = l_Lake_print_x21___closed__7;
x_89 = l_Lean_Name_toString(x_88, x_68, x_66);
x_90 = lean_string_append(x_87, x_89);
lean_dec_ref(x_89);
x_91 = l_Lake_print_x21___closed__8;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_io_error_to_string(x_81);
x_94 = lean_string_append(x_92, x_93);
lean_dec_ref(x_93);
x_95 = l_Lake_print_x21___closed__9;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_String_quote(x_75);
lean_dec_ref(x_75);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_unsigned_to_nat(120u);
x_100 = lean_format_pretty(x_98, x_99, x_35, x_35);
x_101 = lean_string_append(x_96, x_100);
lean_dec_ref(x_100);
x_102 = l_mkPanicMessageWithDecl(x_83, x_84, x_85, x_86, x_101);
lean_dec_ref(x_101);
x_103 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_102, x_82);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set(x_103, 0, x_67);
return x_103;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_67);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
block_120:
{
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_110);
lean_dec(x_16);
if (lean_is_scalar(x_65)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_65;
}
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
else
{
uint8_t x_115; 
lean_dec(x_65);
x_115 = lean_nat_dec_eq(x_110, x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = l_Nat_reprFast(x_110);
x_117 = l_Lake_Workspace_runFetchM___redArg___closed__8;
x_118 = lean_string_append(x_116, x_117);
x_67 = x_109;
x_68 = x_113;
x_69 = x_112;
x_70 = x_118;
goto block_108;
}
else
{
lean_object* x_119; 
lean_dec(x_110);
x_119 = l_Lake_Workspace_runFetchM___redArg___closed__9;
x_67 = x_109;
x_68 = x_113;
x_69 = x_112;
x_70 = x_119;
goto block_108;
}
}
}
block_167:
{
uint8_t x_127; 
x_127 = l_Array_isEmpty___redArg(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_123);
lean_dec(x_65);
lean_dec(x_61);
x_128 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_128);
x_129 = lean_box(x_127);
x_130 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_130, 0, x_129);
x_131 = l_Lake_Workspace_runFetchM___redArg___closed__10;
x_132 = lean_apply_2(x_128, x_131, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec_ref(x_132);
x_36 = x_130;
x_37 = x_125;
x_38 = x_133;
goto block_51;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec_ref(x_132);
x_136 = l_Lake_print_x21___closed__2;
x_137 = l_Lake_print_x21___closed__3;
x_138 = lean_unsigned_to_nat(79u);
x_139 = lean_unsigned_to_nat(4u);
x_140 = l_Lake_print_x21___closed__4;
x_141 = l_Lake_print_x21___closed__7;
lean_inc_ref(x_130);
x_142 = l_Lean_Name_toString(x_141, x_57, x_130);
x_143 = lean_string_append(x_140, x_142);
lean_dec_ref(x_142);
x_144 = l_Lake_print_x21___closed__8;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_io_error_to_string(x_134);
x_147 = lean_string_append(x_145, x_146);
lean_dec_ref(x_146);
x_148 = l_Lake_print_x21___closed__9;
x_149 = lean_string_append(x_147, x_148);
x_150 = l_Lake_Workspace_runFetchM___redArg___closed__13;
x_151 = lean_string_append(x_149, x_150);
x_152 = l_mkPanicMessageWithDecl(x_136, x_137, x_138, x_139, x_151);
lean_dec_ref(x_151);
x_153 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_152, x_135);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec_ref(x_153);
x_36 = x_130;
x_37 = x_125;
x_38 = x_154;
goto block_51;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_125);
x_155 = lean_io_wait(x_61, x_126);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
if (x_122 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec_ref(x_156);
x_109 = x_158;
x_110 = x_123;
x_111 = x_124;
x_112 = x_157;
x_113 = x_122;
goto block_120;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec_ref(x_155);
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
lean_dec_ref(x_156);
x_109 = x_160;
x_110 = x_123;
x_111 = x_124;
x_112 = x_159;
x_113 = x_14;
goto block_120;
}
}
else
{
uint8_t x_161; 
lean_dec_ref(x_156);
lean_dec(x_123);
lean_dec(x_65);
lean_dec(x_16);
x_161 = !lean_is_exclusive(x_155);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_155, 0);
lean_dec(x_162);
x_163 = l_Lake_Workspace_runFetchM___redArg___closed__15;
lean_ctor_set_tag(x_155, 1);
lean_ctor_set(x_155, 0, x_163);
return x_155;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_155, 1);
lean_inc(x_164);
lean_dec(x_155);
x_165 = l_Lake_Workspace_runFetchM___redArg___closed__15;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
block_182:
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_array_get_size(x_169);
x_174 = lean_nat_dec_lt(x_35, x_173);
if (x_174 == 0)
{
lean_dec(x_173);
lean_dec_ref(x_169);
lean_dec(x_24);
x_123 = x_168;
x_124 = x_171;
x_125 = x_170;
x_126 = x_172;
goto block_167;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_173, x_173);
if (x_175 == 0)
{
lean_dec(x_173);
lean_dec_ref(x_169);
lean_dec(x_24);
x_123 = x_168;
x_124 = x_171;
x_125 = x_170;
x_126 = x_172;
goto block_167;
}
else
{
lean_object* x_176; size_t x_177; size_t x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_box(0);
x_177 = 0;
x_178 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_179 = lean_unbox(x_24);
lean_dec(x_24);
lean_inc(x_16);
x_180 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6(x_16, x_11, x_179, x_169, x_177, x_178, x_176, x_172);
lean_dec_ref(x_169);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_123 = x_168;
x_124 = x_171;
x_125 = x_170;
x_126 = x_181;
goto block_167;
}
}
}
block_202:
{
if (x_187 == 0)
{
lean_dec_ref(x_191);
lean_dec(x_24);
x_123 = x_188;
x_124 = x_190;
x_125 = x_189;
x_126 = x_192;
goto block_167;
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_array_get_size(x_191);
x_194 = lean_nat_dec_lt(x_35, x_193);
if (x_194 == 0)
{
lean_dec(x_193);
lean_dec_ref(x_191);
lean_dec(x_24);
x_123 = x_188;
x_124 = x_190;
x_125 = x_189;
x_126 = x_192;
goto block_167;
}
else
{
uint8_t x_195; 
x_195 = lean_nat_dec_le(x_193, x_193);
if (x_195 == 0)
{
lean_dec(x_193);
lean_dec_ref(x_191);
lean_dec(x_24);
x_123 = x_188;
x_124 = x_190;
x_125 = x_189;
x_126 = x_192;
goto block_167;
}
else
{
lean_object* x_196; size_t x_197; size_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_196 = lean_box(0);
x_197 = 0;
x_198 = lean_usize_of_nat(x_193);
lean_dec(x_193);
x_199 = lean_unbox(x_24);
lean_dec(x_24);
lean_inc(x_16);
x_200 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6(x_16, x_11, x_199, x_191, x_197, x_198, x_196, x_192);
lean_dec_ref(x_191);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
x_123 = x_188;
x_124 = x_190;
x_125 = x_189;
x_126 = x_201;
goto block_167;
}
}
}
}
block_270:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_204 = lean_ctor_get(x_27, 3);
lean_inc(x_204);
lean_dec(x_27);
x_205 = l_Lake_Job_toOpaque___redArg(x_185);
x_206 = lean_unsigned_to_nat(1u);
x_207 = l_Lake_Workspace_runFetchM___redArg___closed__17;
x_208 = lean_array_push(x_207, x_205);
x_209 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_210 = lean_unsigned_to_nat(100u);
x_211 = lean_unbox(x_24);
lean_inc(x_16);
x_212 = l_Lake_monitorJobs(x_208, x_204, x_16, x_10, x_11, x_203, x_187, x_211, x_122, x_209, x_54, x_210, x_64);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = lean_ctor_get(x_213, 0);
lean_inc_ref(x_215);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_dec(x_213);
x_217 = l_Lake_Workspace_saveInputs(x_1, x_54, x_214);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec_ref(x_217);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_array_get_size(x_220);
x_222 = lean_nat_dec_eq(x_221, x_35);
lean_dec(x_221);
if (x_222 == 0)
{
if (x_187 == 0)
{
lean_dec(x_220);
lean_dec(x_24);
x_123 = x_216;
x_124 = x_206;
x_125 = x_215;
x_126 = x_219;
goto block_167;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_223);
x_224 = l_Lake_Workspace_runFetchM___redArg___closed__18;
x_225 = lean_apply_2(x_223, x_224, x_219);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec_ref(x_225);
x_168 = x_216;
x_169 = x_220;
x_170 = x_215;
x_171 = x_206;
x_172 = x_226;
goto block_182;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec_ref(x_225);
x_229 = l_Lake_print_x21___closed__2;
x_230 = l_Lake_print_x21___closed__3;
x_231 = lean_unsigned_to_nat(79u);
x_232 = lean_unsigned_to_nat(4u);
x_233 = l_Lake_print_x21___closed__4;
x_234 = l_Lake_print_x21___closed__7;
x_235 = l_Lean_Name_toString(x_234, x_187, x_66);
x_236 = lean_string_append(x_233, x_235);
lean_dec_ref(x_235);
x_237 = l_Lake_print_x21___closed__8;
x_238 = lean_string_append(x_236, x_237);
x_239 = lean_io_error_to_string(x_227);
x_240 = lean_string_append(x_238, x_239);
lean_dec_ref(x_239);
x_241 = l_Lake_print_x21___closed__9;
x_242 = lean_string_append(x_240, x_241);
x_243 = l_Lake_Workspace_runFetchM___redArg___closed__21;
x_244 = lean_string_append(x_242, x_243);
x_245 = l_mkPanicMessageWithDecl(x_229, x_230, x_231, x_232, x_244);
lean_dec_ref(x_244);
x_246 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_245, x_228);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec_ref(x_246);
x_168 = x_216;
x_169 = x_220;
x_170 = x_215;
x_171 = x_206;
x_172 = x_247;
goto block_182;
}
}
}
else
{
lean_dec(x_220);
lean_dec(x_24);
x_123 = x_216;
x_124 = x_206;
x_125 = x_215;
x_126 = x_219;
goto block_167;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_217, 1);
lean_inc(x_248);
lean_dec_ref(x_217);
x_249 = lean_ctor_get(x_218, 1);
lean_inc(x_249);
lean_dec_ref(x_218);
x_250 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_250);
x_251 = l_Lake_Workspace_runFetchM___redArg___closed__22;
x_252 = lean_apply_2(x_250, x_251, x_248);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec_ref(x_252);
x_188 = x_216;
x_189 = x_215;
x_190 = x_206;
x_191 = x_249;
x_192 = x_253;
goto block_202;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_dec_ref(x_252);
x_256 = l_Lake_print_x21___closed__2;
x_257 = l_Lake_print_x21___closed__3;
x_258 = lean_unsigned_to_nat(79u);
x_259 = lean_unsigned_to_nat(4u);
x_260 = l_Lake_Monitor_print___closed__3;
x_261 = lean_io_error_to_string(x_254);
x_262 = lean_string_append(x_260, x_261);
lean_dec_ref(x_261);
x_263 = l_Lake_print_x21___closed__9;
x_264 = lean_string_append(x_262, x_263);
x_265 = l_Lake_Workspace_runFetchM___redArg___closed__25;
x_266 = lean_string_append(x_264, x_265);
x_267 = l_mkPanicMessageWithDecl(x_256, x_257, x_258, x_259, x_266);
lean_dec_ref(x_266);
x_268 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_267, x_255);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec_ref(x_268);
x_188 = x_216;
x_189 = x_215;
x_190 = x_206;
x_191 = x_249;
x_192 = x_269;
goto block_202;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__6(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_Workspace_runFetchM___redArg___lam__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = lean_io_wait(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec_ref(x_10);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = l_Lake_Workspace_runFetchM___redArg___closed__1;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = lean_io_wait(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_11);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = l_Lake_Workspace_runFetchM___redArg___closed__1;
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
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
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_3, x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = lean_io_wait(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec_ref(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec_ref(x_10);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = l_Lake_Workspace_runFetchM___redArg___closed__1;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_4, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = lean_io_wait(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_11);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = l_Lake_Workspace_runFetchM___redArg___closed__1;
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
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
lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Index(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Lock(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkBuildContext___closed__0 = _init_l_Lake_mkBuildContext___closed__0();
lean_mark_persistent(l_Lake_mkBuildContext___closed__0);
l_Lake_mkBuildContext___closed__1 = _init_l_Lake_mkBuildContext___closed__1();
lean_mark_persistent(l_Lake_mkBuildContext___closed__1);
l_Lake_mkBuildContext___closed__2 = _init_l_Lake_mkBuildContext___closed__2();
lean_mark_persistent(l_Lake_mkBuildContext___closed__2);
l_Lake_mkBuildContext___closed__3 = _init_l_Lake_mkBuildContext___closed__3();
lean_mark_persistent(l_Lake_mkBuildContext___closed__3);
l_Lake_mkBuildContext___closed__4 = _init_l_Lake_mkBuildContext___closed__4();
lean_mark_persistent(l_Lake_mkBuildContext___closed__4);
l_Lake_mkBuildContext___closed__5 = _init_l_Lake_mkBuildContext___closed__5();
lean_mark_persistent(l_Lake_mkBuildContext___closed__5);
l_Lake_mkBuildContext___closed__6 = _init_l_Lake_mkBuildContext___closed__6();
lean_mark_persistent(l_Lake_mkBuildContext___closed__6);
l_Lake_Monitor_spinnerFrames___closed__0 = _init_l_Lake_Monitor_spinnerFrames___closed__0();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__0);
l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__1 = _init_l_Lake_Monitor_spinnerFrames___closed__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__1);
l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__2 = _init_l_Lake_Monitor_spinnerFrames___closed__2();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__2);
l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__3 = _init_l_Lake_Monitor_spinnerFrames___closed__3();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__3);
l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__4 = _init_l_Lake_Monitor_spinnerFrames___closed__4();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__4);
l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__5 = _init_l_Lake_Monitor_spinnerFrames___closed__5();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__5);
l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__6 = _init_l_Lake_Monitor_spinnerFrames___closed__6();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__6);
l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__7 = _init_l_Lake_Monitor_spinnerFrames___closed__7();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__7);
l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1 = _init_l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1);
l_Lake_Monitor_spinnerFrames___closed__8 = _init_l_Lake_Monitor_spinnerFrames___closed__8();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__8);
l_Lake_Monitor_spinnerFrames = _init_l_Lake_Monitor_spinnerFrames();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames);
l_Lake_Ansi_resetLine___closed__0 = _init_l_Lake_Ansi_resetLine___closed__0();
lean_mark_persistent(l_Lake_Ansi_resetLine___closed__0);
l_Lake_Ansi_resetLine = _init_l_Lake_Ansi_resetLine();
lean_mark_persistent(l_Lake_Ansi_resetLine);
l_Lake_print_x21___closed__0 = _init_l_Lake_print_x21___closed__0();
lean_mark_persistent(l_Lake_print_x21___closed__0);
l_Lake_print_x21___closed__1 = _init_l_Lake_print_x21___closed__1();
lean_mark_persistent(l_Lake_print_x21___closed__1);
l_Lake_print_x21___closed__2 = _init_l_Lake_print_x21___closed__2();
lean_mark_persistent(l_Lake_print_x21___closed__2);
l_Lake_print_x21___closed__3 = _init_l_Lake_print_x21___closed__3();
lean_mark_persistent(l_Lake_print_x21___closed__3);
l_Lake_print_x21___closed__4 = _init_l_Lake_print_x21___closed__4();
lean_mark_persistent(l_Lake_print_x21___closed__4);
l_Lake_print_x21___closed__5 = _init_l_Lake_print_x21___closed__5();
lean_mark_persistent(l_Lake_print_x21___closed__5);
l_Lake_print_x21___closed__6 = _init_l_Lake_print_x21___closed__6();
lean_mark_persistent(l_Lake_print_x21___closed__6);
l_Lake_print_x21___closed__7 = _init_l_Lake_print_x21___closed__7();
lean_mark_persistent(l_Lake_print_x21___closed__7);
l_Lake_print_x21___closed__8 = _init_l_Lake_print_x21___closed__8();
lean_mark_persistent(l_Lake_print_x21___closed__8);
l_Lake_print_x21___closed__9 = _init_l_Lake_print_x21___closed__9();
lean_mark_persistent(l_Lake_print_x21___closed__9);
l_Lake_Monitor_print___closed__0 = _init_l_Lake_Monitor_print___closed__0();
lean_mark_persistent(l_Lake_Monitor_print___closed__0);
l_Lake_Monitor_print___closed__1 = _init_l_Lake_Monitor_print___closed__1();
lean_mark_persistent(l_Lake_Monitor_print___closed__1);
l_Lake_Monitor_print___closed__2 = _init_l_Lake_Monitor_print___closed__2();
lean_mark_persistent(l_Lake_Monitor_print___closed__2);
l_Lake_Monitor_print___closed__3 = _init_l_Lake_Monitor_print___closed__3();
lean_mark_persistent(l_Lake_Monitor_print___closed__3);
l_Lake_Monitor_renderProgress___redArg___closed__0 = _init_l_Lake_Monitor_renderProgress___redArg___closed__0();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__0);
l_Lake_Monitor_renderProgress___redArg___closed__1 = _init_l_Lake_Monitor_renderProgress___redArg___closed__1();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__1);
l_Lake_Monitor_renderProgress___redArg___closed__2 = _init_l_Lake_Monitor_renderProgress___redArg___closed__2();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__2);
l_Lake_Monitor_renderProgress___redArg___closed__3 = _init_l_Lake_Monitor_renderProgress___redArg___closed__3();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__3);
l_Lake_Monitor_renderProgress___redArg___closed__4 = _init_l_Lake_Monitor_renderProgress___redArg___closed__4();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__4);
l_Lake_Monitor_renderProgress___redArg___closed__5 = _init_l_Lake_Monitor_renderProgress___redArg___closed__5();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__5);
l_Lake_Monitor_renderProgress___redArg___closed__6 = _init_l_Lake_Monitor_renderProgress___redArg___closed__6();
lean_mark_persistent(l_Lake_Monitor_renderProgress___redArg___closed__6);
l_Lake_Monitor_reportJob___closed__0 = _init_l_Lake_Monitor_reportJob___closed__0();
lean_mark_persistent(l_Lake_Monitor_reportJob___closed__0);
l_Lake_Monitor_reportJob___closed__1 = _init_l_Lake_Monitor_reportJob___closed__1();
lean_mark_persistent(l_Lake_Monitor_reportJob___closed__1);
l_Lake_Monitor_reportJob___closed__2 = _init_l_Lake_Monitor_reportJob___closed__2();
lean_mark_persistent(l_Lake_Monitor_reportJob___closed__2);
l_Lake_Monitor_reportJob___closed__3 = _init_l_Lake_Monitor_reportJob___closed__3();
lean_mark_persistent(l_Lake_Monitor_reportJob___closed__3);
l_Lake_Monitor_reportJob___closed__4 = _init_l_Lake_Monitor_reportJob___closed__4();
lean_mark_persistent(l_Lake_Monitor_reportJob___closed__4);
l_Lake_Monitor_poll___closed__0 = _init_l_Lake_Monitor_poll___closed__0();
lean_mark_persistent(l_Lake_Monitor_poll___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4);
l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0);
l_Lake_Workspace_runFetchM___redArg___closed__0 = _init_l_Lake_Workspace_runFetchM___redArg___closed__0();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__0);
l_Lake_Workspace_runFetchM___redArg___closed__1 = _init_l_Lake_Workspace_runFetchM___redArg___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__1);
l_Lake_Workspace_runFetchM___redArg___closed__2 = _init_l_Lake_Workspace_runFetchM___redArg___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__2);
l_Lake_Workspace_runFetchM___redArg___closed__3 = _init_l_Lake_Workspace_runFetchM___redArg___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__3);
l_Lake_Workspace_runFetchM___redArg___closed__4 = _init_l_Lake_Workspace_runFetchM___redArg___closed__4();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__4);
l_Lake_Workspace_runFetchM___redArg___closed__5 = _init_l_Lake_Workspace_runFetchM___redArg___closed__5();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__5);
l_Lake_Workspace_runFetchM___redArg___closed__6 = _init_l_Lake_Workspace_runFetchM___redArg___closed__6();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__6);
l_Lake_Workspace_runFetchM___redArg___closed__7 = _init_l_Lake_Workspace_runFetchM___redArg___closed__7();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__7);
l_Lake_Workspace_runFetchM___redArg___closed__8 = _init_l_Lake_Workspace_runFetchM___redArg___closed__8();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__8);
l_Lake_Workspace_runFetchM___redArg___closed__9 = _init_l_Lake_Workspace_runFetchM___redArg___closed__9();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__9);
l_Lake_Workspace_runFetchM___redArg___closed__10 = _init_l_Lake_Workspace_runFetchM___redArg___closed__10();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__10);
l_Lake_Workspace_runFetchM___redArg___closed__11 = _init_l_Lake_Workspace_runFetchM___redArg___closed__11();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__11);
l_Lake_Workspace_runFetchM___redArg___closed__12 = _init_l_Lake_Workspace_runFetchM___redArg___closed__12();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__12);
l_Lake_Workspace_runFetchM___redArg___closed__13 = _init_l_Lake_Workspace_runFetchM___redArg___closed__13();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__13);
l_Lake_Workspace_runFetchM___redArg___closed__14 = _init_l_Lake_Workspace_runFetchM___redArg___closed__14();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__14);
l_Lake_Workspace_runFetchM___redArg___closed__15 = _init_l_Lake_Workspace_runFetchM___redArg___closed__15();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__15);
l_Lake_Workspace_runFetchM___redArg___closed__16 = _init_l_Lake_Workspace_runFetchM___redArg___closed__16();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__16);
l_Lake_Workspace_runFetchM___redArg___closed__17 = _init_l_Lake_Workspace_runFetchM___redArg___closed__17();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__17);
l_Lake_Workspace_runFetchM___redArg___closed__18 = _init_l_Lake_Workspace_runFetchM___redArg___closed__18();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__18);
l_Lake_Workspace_runFetchM___redArg___closed__19 = _init_l_Lake_Workspace_runFetchM___redArg___closed__19();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__19);
l_Lake_Workspace_runFetchM___redArg___closed__20 = _init_l_Lake_Workspace_runFetchM___redArg___closed__20();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__20);
l_Lake_Workspace_runFetchM___redArg___closed__21 = _init_l_Lake_Workspace_runFetchM___redArg___closed__21();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__21);
l_Lake_Workspace_runFetchM___redArg___closed__22 = _init_l_Lake_Workspace_runFetchM___redArg___closed__22();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__22);
l_Lake_Workspace_runFetchM___redArg___closed__23 = _init_l_Lake_Workspace_runFetchM___redArg___closed__23();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__23);
l_Lake_Workspace_runFetchM___redArg___closed__24 = _init_l_Lake_Workspace_runFetchM___redArg___closed__24();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__24);
l_Lake_Workspace_runFetchM___redArg___closed__25 = _init_l_Lake_Workspace_runFetchM___redArg___closed__25();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__25);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
