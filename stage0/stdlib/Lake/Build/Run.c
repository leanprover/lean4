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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__0;
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__4;
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__1;
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__2;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(uint8_t, uint8_t);
lean_object* l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__3;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__13;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint64_t lean_string_hash(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__6;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__4;
static lean_object* l_Lake_Monitor_print___closed__1;
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__5;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__6;
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
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
lean_object* lean_io_mono_ms_now(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__6;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_print_x21___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lake_print_x21___closed__8;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__0;
static lean_object* l_Lake_print_x21___closed__6;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__4;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__11;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_reportJob___closed__2;
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__9;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__7;
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_mkBuildContext___closed__0;
uint8_t l_Lake_ordLogLevel____x40_Lake_Util_Log___hyg_764_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__8;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_resetLine;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__8;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__0;
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___redArg___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_recFetch___at___Lake_recFetchAcyclic___at___Lake_recFetchWithIndex_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__3;
static lean_object* l_Lake_Monitor_print___closed__2;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lake_Env_leanGithash(x_8);
lean_dec(x_8);
x_10 = 1723;
x_11 = lean_string_hash(x_9);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = l_Lake_mkBuildContext___closed__4;
x_14 = lean_string_append(x_13, x_9);
lean_dec(x_9);
x_15 = l_Lake_mkBuildContext___closed__6;
x_16 = lean_box_uint64(x_12);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_7);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = l_Lake_Env_leanGithash(x_21);
lean_dec(x_21);
x_23 = 1723;
x_24 = lean_string_hash(x_22);
x_25 = lean_uint64_mix_hash(x_23, x_24);
x_26 = l_Lake_mkBuildContext___closed__4;
x_27 = lean_string_append(x_26, x_22);
lean_dec(x_22);
x_28 = l_Lake_mkBuildContext___closed__6;
x_29 = lean_box_uint64(x_25);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_28);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_19);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
return x_32;
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
lean_inc(x_3);
lean_dec(x_1);
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
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
lean_inc(x_4);
lean_dec(x_1);
lean_inc(x_2);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_13 = l_Lake_print_x21___closed__1;
x_14 = l_Lake_print_x21___closed__2;
x_15 = l_Lake_print_x21___closed__3;
x_16 = lean_unsigned_to_nat(79u);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lake_print_x21___closed__4;
x_19 = l_Lake_print_x21___closed__7;
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Name_toString(x_19, x_21, x_12);
x_23 = lean_string_append(x_18, x_22);
lean_dec(x_22);
x_24 = l_Lake_print_x21___closed__8;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_io_error_to_string(x_10);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Lake_print_x21___closed__9;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_String_quote(x_2);
lean_dec(x_2);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unsigned_to_nat(120u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_format_pretty(x_31, x_32, x_33, x_33);
x_35 = lean_string_append(x_29, x_34);
lean_dec(x_34);
x_36 = l_mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_35);
lean_dec(x_35);
x_37 = l_panic___redArg(x_13, x_36);
x_38 = lean_apply_1(x_37, x_11);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lake_print_x21___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_print_x21___lam__0(x_1);
lean_dec(x_1);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lake_Monitor_print___closed__0;
x_2 = lean_box(1);
x_3 = l_Lake_print_x21___closed__7;
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Name_toString(x_3, x_4, x_1);
return x_5;
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
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = lean_apply_2(x_11, x_1, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
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
lean_dec(x_12);
x_17 = l_Lake_print_x21___closed__1;
x_18 = l_Lake_print_x21___closed__2;
x_19 = l_Lake_print_x21___closed__3;
x_20 = lean_unsigned_to_nat(79u);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lake_Monitor_print___closed__3;
x_23 = lean_io_error_to_string(x_15);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_Lake_print_x21___closed__9;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_String_quote(x_1);
lean_dec(x_1);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unsigned_to_nat(120u);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_format_pretty(x_28, x_29, x_30, x_30);
x_32 = lean_string_append(x_26, x_31);
lean_dec(x_31);
x_33 = l_mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_32);
lean_dec(x_32);
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
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_1(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_4 = x_12;
x_5 = x_13;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
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
lean_dec(x_3);
goto block_9;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
if (x_11 == 0)
{
lean_dec(x_3);
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
lean_inc(x_17);
lean_dec(x_3);
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
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_90 = lean_string_append(x_89, x_88);
lean_dec(x_88);
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
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = l_Lake_Monitor_renderProgress___redArg___closed__5;
x_97 = lean_string_append(x_95, x_96);
x_98 = l_Nat_reprFast(x_91);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
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
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_apply_1(x_32, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_26 = x_34;
x_27 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
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
lean_inc(x_40);
x_41 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_42 = lean_string_push(x_41, x_22);
x_43 = lean_string_append(x_15, x_42);
lean_dec(x_42);
x_44 = l_Lake_Monitor_renderProgress___redArg___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_Nat_reprFast(x_13);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l_Lake_Monitor_renderProgress___redArg___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Nat_reprFast(x_14);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = l_Lake_print_x21___closed__9;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_39);
lean_dec(x_39);
lean_inc(x_54);
x_55 = lean_apply_2(x_40, x_54, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
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
lean_dec(x_55);
x_59 = l_Lake_print_x21___closed__2;
x_60 = l_Lake_print_x21___closed__3;
x_61 = lean_unsigned_to_nat(79u);
x_62 = lean_unsigned_to_nat(4u);
x_63 = l_Lake_print_x21___closed__4;
x_64 = l_Lake_print_x21___closed__7;
x_65 = l_Lean_Name_toString(x_64, x_11, x_18);
x_66 = lean_string_append(x_63, x_65);
lean_dec(x_65);
x_67 = l_Lake_print_x21___closed__8;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_io_error_to_string(x_57);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_string_append(x_70, x_52);
x_72 = l_String_quote(x_54);
lean_dec(x_54);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_unsigned_to_nat(120u);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_format_pretty(x_73, x_74, x_75, x_75);
x_77 = lean_string_append(x_71, x_76);
lean_dec(x_76);
x_78 = l_mkPanicMessageWithDecl(x_59, x_60, x_61, x_62, x_77);
lean_dec(x_77);
x_79 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_78, x_58);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
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
lean_inc(x_108);
lean_dec(x_3);
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
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
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
lean_inc(x_185);
lean_dec(x_184);
x_186 = l_Lake_Monitor_renderProgress___redArg___closed__4;
x_187 = lean_string_append(x_186, x_185);
lean_dec(x_185);
x_188 = l_Lake_Monitor_renderProgress___redArg___closed__5;
x_189 = lean_string_append(x_187, x_188);
x_190 = l_Nat_reprFast(x_183);
x_191 = lean_string_append(x_189, x_190);
lean_dec(x_190);
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
lean_inc(x_124);
lean_dec(x_108);
x_125 = lean_apply_1(x_124, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_118 = x_126;
x_119 = x_127;
goto block_122;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
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
lean_inc(x_132);
x_133 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_134 = lean_string_push(x_133, x_113);
x_135 = lean_string_append(x_105, x_134);
lean_dec(x_134);
x_136 = l_Lake_Monitor_renderProgress___redArg___closed__2;
x_137 = lean_string_append(x_135, x_136);
x_138 = l_Nat_reprFast(x_102);
x_139 = lean_string_append(x_137, x_138);
lean_dec(x_138);
x_140 = l_Lake_Monitor_renderProgress___redArg___closed__3;
x_141 = lean_string_append(x_139, x_140);
x_142 = l_Nat_reprFast(x_103);
x_143 = lean_string_append(x_141, x_142);
lean_dec(x_142);
x_144 = l_Lake_print_x21___closed__9;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_131);
lean_dec(x_131);
lean_inc(x_146);
x_147 = lean_apply_2(x_132, x_146, x_5);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
lean_dec(x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
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
lean_dec(x_147);
x_151 = l_Lake_print_x21___closed__2;
x_152 = l_Lake_print_x21___closed__3;
x_153 = lean_unsigned_to_nat(79u);
x_154 = lean_unsigned_to_nat(4u);
x_155 = l_Lake_print_x21___closed__4;
x_156 = l_Lake_print_x21___closed__7;
x_157 = l_Lean_Name_toString(x_156, x_11, x_109);
x_158 = lean_string_append(x_155, x_157);
lean_dec(x_157);
x_159 = l_Lake_print_x21___closed__8;
x_160 = lean_string_append(x_158, x_159);
x_161 = lean_io_error_to_string(x_149);
x_162 = lean_string_append(x_160, x_161);
lean_dec(x_161);
x_163 = lean_string_append(x_162, x_144);
x_164 = l_String_quote(x_146);
lean_dec(x_146);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_unsigned_to_nat(120u);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_format_pretty(x_165, x_166, x_167, x_167);
x_169 = lean_string_append(x_163, x_168);
lean_dec(x_168);
x_170 = l_mkPanicMessageWithDecl(x_151, x_152, x_153, x_154, x_169);
lean_dec(x_169);
x_171 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_170, x_150);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
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
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Monitor_renderProgress(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_7);
x_11 = lean_array_uget(x_4, x_5);
lean_inc(x_1);
x_12 = l_Lake_logToStream(x_11, x_1, x_2, x_3, x_9);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
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
lean_dec(x_1);
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
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_152; uint32_t x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_183; uint8_t x_184; uint8_t x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; uint32_t x_192; lean_object* x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; uint8_t x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; uint8_t x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_316; uint8_t x_317; uint8_t x_318; uint8_t x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; lean_object* x_333; uint8_t x_334; uint8_t x_347; uint8_t x_348; uint8_t x_349; uint8_t x_350; lean_object* x_351; uint8_t x_352; uint8_t x_360; uint8_t x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; uint8_t x_370; uint8_t x_371; lean_object* x_372; uint8_t x_373; lean_object* x_379; lean_object* x_388; lean_object* x_389; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_218 = lean_box(1);
x_219 = lean_box(0);
x_388 = lean_task_get_own(x_67);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
x_379 = x_389;
goto block_387;
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_1(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_11 = x_18;
x_12 = x_23;
x_13 = x_24;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_11 = x_18;
x_12 = x_26;
x_13 = x_25;
goto block_16;
}
}
block_57:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_44);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_34);
x_17 = x_43;
x_18 = x_42;
x_19 = x_41;
goto block_27;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_34);
x_17 = x_43;
x_18 = x_42;
x_19 = x_41;
goto block_27;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_box(0);
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_53 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_34, x_45, x_39, x_44, x_51, x_52, x_50, x_42, x_41);
lean_dec(x_44);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_17 = x_43;
x_18 = x_56;
x_19 = x_55;
goto block_27;
}
}
}
block_66:
{
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_34);
x_17 = x_60;
x_18 = x_59;
x_19 = x_63;
goto block_27;
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
lean_object* x_64; uint8_t x_65; 
x_64 = lean_box(0);
x_65 = lean_unbox(x_64);
x_41 = x_63;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_65;
goto block_57;
}
}
}
block_140:
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
x_79 = !lean_is_exclusive(x_70);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_70, 3);
x_81 = lean_ctor_get(x_78, 4);
lean_inc(x_81);
lean_dec(x_78);
lean_ctor_set(x_70, 3, x_73);
x_82 = lean_string_append(x_80, x_77);
lean_dec(x_77);
x_83 = l_Lake_Monitor_reportJob___closed__0;
x_84 = lean_string_append(x_82, x_83);
lean_inc(x_84);
x_85 = lean_apply_2(x_81, x_84, x_74);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec(x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_58 = x_71;
x_59 = x_70;
x_60 = x_72;
x_61 = x_75;
x_62 = x_76;
x_63 = x_86;
goto block_66;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lake_print_x21___closed__2;
x_90 = l_Lake_print_x21___closed__3;
x_91 = lean_unsigned_to_nat(79u);
x_92 = lean_unsigned_to_nat(4u);
x_93 = l_Lake_Monitor_print___closed__3;
x_94 = lean_io_error_to_string(x_87);
x_95 = lean_string_append(x_93, x_94);
lean_dec(x_94);
x_96 = l_Lake_print_x21___closed__9;
x_97 = lean_string_append(x_95, x_96);
x_98 = l_String_quote(x_84);
lean_dec(x_84);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_unsigned_to_nat(120u);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_format_pretty(x_99, x_100, x_101, x_101);
x_103 = lean_string_append(x_97, x_102);
lean_dec(x_102);
x_104 = l_mkPanicMessageWithDecl(x_89, x_90, x_91, x_92, x_103);
lean_dec(x_103);
x_105 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_104, x_88);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_58 = x_71;
x_59 = x_70;
x_60 = x_72;
x_61 = x_75;
x_62 = x_76;
x_63 = x_106;
goto block_66;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_107 = lean_ctor_get(x_70, 0);
x_108 = lean_ctor_get(x_70, 1);
x_109 = lean_ctor_get(x_70, 2);
x_110 = lean_ctor_get(x_70, 3);
x_111 = lean_ctor_get(x_70, 4);
x_112 = lean_ctor_get(x_70, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_70);
x_113 = lean_ctor_get(x_78, 4);
lean_inc(x_113);
lean_dec(x_78);
x_114 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_108);
lean_ctor_set(x_114, 2, x_109);
lean_ctor_set(x_114, 3, x_73);
lean_ctor_set(x_114, 4, x_111);
lean_ctor_set(x_114, 5, x_112);
x_115 = lean_string_append(x_110, x_77);
lean_dec(x_77);
x_116 = l_Lake_Monitor_reportJob___closed__0;
x_117 = lean_string_append(x_115, x_116);
lean_inc(x_117);
x_118 = lean_apply_2(x_113, x_117, x_74);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_dec(x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_58 = x_71;
x_59 = x_114;
x_60 = x_72;
x_61 = x_75;
x_62 = x_76;
x_63 = x_119;
goto block_66;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = l_Lake_print_x21___closed__2;
x_123 = l_Lake_print_x21___closed__3;
x_124 = lean_unsigned_to_nat(79u);
x_125 = lean_unsigned_to_nat(4u);
x_126 = l_Lake_Monitor_print___closed__3;
x_127 = lean_io_error_to_string(x_120);
x_128 = lean_string_append(x_126, x_127);
lean_dec(x_127);
x_129 = l_Lake_print_x21___closed__9;
x_130 = lean_string_append(x_128, x_129);
x_131 = l_String_quote(x_117);
lean_dec(x_117);
x_132 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_unsigned_to_nat(120u);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_format_pretty(x_132, x_133, x_134, x_134);
x_136 = lean_string_append(x_130, x_135);
lean_dec(x_135);
x_137 = l_mkPanicMessageWithDecl(x_122, x_123, x_124, x_125, x_136);
lean_dec(x_136);
x_138 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_137, x_121);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_58 = x_71;
x_59 = x_114;
x_60 = x_72;
x_61 = x_75;
x_62 = x_76;
x_63 = x_139;
goto block_66;
}
}
}
block_151:
{
lean_object* x_150; 
x_150 = l_Lake_Ansi_chalk(x_149, x_142);
lean_dec(x_142);
lean_dec(x_149);
x_70 = x_141;
x_71 = x_143;
x_72 = x_144;
x_73 = x_145;
x_74 = x_147;
x_75 = x_146;
x_76 = x_148;
x_77 = x_150;
goto block_140;
}
block_182:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_162 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_163 = lean_string_push(x_162, x_153);
x_164 = l_Lake_Monitor_renderProgress___redArg___closed__2;
x_165 = lean_string_append(x_163, x_164);
x_166 = l_Nat_reprFast(x_28);
x_167 = lean_string_append(x_165, x_166);
lean_dec(x_166);
x_168 = l_Lake_Monitor_renderProgress___redArg___closed__3;
x_169 = lean_string_append(x_167, x_168);
x_170 = l_Nat_reprFast(x_29);
x_171 = lean_string_append(x_169, x_170);
lean_dec(x_170);
x_172 = l_Lake_Monitor_reportJob___closed__1;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_string_append(x_173, x_161);
lean_dec(x_161);
x_175 = l_Lake_Monitor_reportJob___closed__2;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_string_append(x_176, x_159);
lean_dec(x_159);
x_178 = lean_string_append(x_177, x_175);
x_179 = lean_string_append(x_178, x_68);
lean_dec(x_68);
if (x_39 == 0)
{
x_70 = x_152;
x_71 = x_154;
x_72 = x_156;
x_73 = x_162;
x_74 = x_158;
x_75 = x_157;
x_76 = x_160;
x_77 = x_179;
goto block_140;
}
else
{
if (x_160 == 0)
{
lean_object* x_180; 
x_180 = l_Lake_Monitor_reportJob___closed__3;
x_141 = x_152;
x_142 = x_179;
x_143 = x_154;
x_144 = x_156;
x_145 = x_162;
x_146 = x_157;
x_147 = x_158;
x_148 = x_160;
x_149 = x_180;
goto block_151;
}
else
{
lean_object* x_181; 
x_181 = l_Lake_LogLevel_ansiColor(x_155);
x_141 = x_152;
x_142 = x_179;
x_143 = x_154;
x_144 = x_156;
x_145 = x_162;
x_146 = x_157;
x_147 = x_158;
x_148 = x_160;
x_149 = x_181;
goto block_151;
}
}
}
block_195:
{
if (x_184 == 0)
{
lean_object* x_193; 
x_193 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_152 = x_183;
x_153 = x_192;
x_154 = x_185;
x_155 = x_187;
x_156 = x_186;
x_157 = x_189;
x_158 = x_188;
x_159 = x_191;
x_160 = x_190;
x_161 = x_193;
goto block_182;
}
else
{
lean_object* x_194; 
x_194 = l_Lake_Monitor_reportJob___closed__4;
x_152 = x_183;
x_153 = x_192;
x_154 = x_185;
x_155 = x_187;
x_156 = x_186;
x_157 = x_189;
x_158 = x_188;
x_159 = x_191;
x_160 = x_190;
x_161 = x_194;
goto block_182;
}
}
block_206:
{
uint32_t x_205; 
x_205 = l_Lake_LogLevel_icon(x_199);
x_183 = x_196;
x_184 = x_197;
x_185 = x_198;
x_186 = x_200;
x_187 = x_199;
x_188 = x_202;
x_189 = x_201;
x_190 = x_204;
x_191 = x_203;
x_192 = x_205;
goto block_195;
}
block_217:
{
uint32_t x_216; 
x_216 = 10004;
x_183 = x_207;
x_184 = x_208;
x_185 = x_209;
x_186 = x_211;
x_187 = x_210;
x_188 = x_213;
x_189 = x_212;
x_190 = x_215;
x_191 = x_214;
x_192 = x_216;
goto block_195;
}
block_247:
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; 
x_229 = lean_array_get_size(x_228);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_nat_dec_eq(x_229, x_230);
lean_dec(x_229);
x_232 = l_instDecidableNot___redArg(x_231);
if (x_232 == 0)
{
uint8_t x_233; lean_object* x_234; uint8_t x_235; uint8_t x_236; 
x_233 = lean_unbox(x_219);
x_234 = l_Lake_JobAction_verb(x_233, x_221);
x_235 = lean_unbox(x_219);
x_236 = lean_unbox(x_219);
x_207 = x_220;
x_208 = x_222;
x_209 = x_235;
x_210 = x_226;
x_211 = x_225;
x_212 = x_228;
x_213 = x_227;
x_214 = x_234;
x_215 = x_236;
goto block_217;
}
else
{
if (x_223 == 0)
{
uint8_t x_237; lean_object* x_238; 
x_237 = lean_unbox(x_219);
x_238 = l_Lake_JobAction_verb(x_237, x_221);
if (x_224 == 0)
{
uint8_t x_239; uint8_t x_240; 
x_239 = lean_unbox(x_219);
x_240 = lean_unbox(x_219);
x_207 = x_220;
x_208 = x_222;
x_209 = x_239;
x_210 = x_226;
x_211 = x_225;
x_212 = x_228;
x_213 = x_227;
x_214 = x_238;
x_215 = x_240;
goto block_217;
}
else
{
uint8_t x_241; uint8_t x_242; 
x_241 = lean_unbox(x_219);
x_242 = lean_unbox(x_218);
x_196 = x_220;
x_197 = x_222;
x_198 = x_241;
x_199 = x_226;
x_200 = x_225;
x_201 = x_228;
x_202 = x_227;
x_203 = x_238;
x_204 = x_242;
goto block_206;
}
}
else
{
uint8_t x_243; lean_object* x_244; uint8_t x_245; uint8_t x_246; 
x_243 = lean_unbox(x_218);
x_244 = l_Lake_JobAction_verb(x_243, x_221);
x_245 = lean_unbox(x_218);
x_246 = lean_unbox(x_218);
x_196 = x_220;
x_197 = x_222;
x_198 = x_245;
x_199 = x_226;
x_200 = x_225;
x_201 = x_228;
x_202 = x_227;
x_203 = x_244;
x_204 = x_246;
goto block_206;
}
}
}
block_260:
{
uint8_t x_259; 
x_259 = l_instDecidableNot___redArg(x_258);
if (x_259 == 0)
{
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_249;
x_6 = x_257;
goto block_10;
}
else
{
if (x_252 == 0)
{
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_249;
x_6 = x_257;
goto block_10;
}
else
{
x_220 = x_249;
x_221 = x_248;
x_222 = x_251;
x_223 = x_250;
x_224 = x_255;
x_225 = x_254;
x_226 = x_253;
x_227 = x_257;
x_228 = x_256;
goto block_247;
}
}
}
block_273:
{
if (x_40 == 0)
{
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_262;
x_6 = x_270;
goto block_10;
}
else
{
if (x_39 == 0)
{
uint8_t x_271; 
x_271 = lean_unbox(x_219);
x_248 = x_261;
x_249 = x_262;
x_250 = x_264;
x_251 = x_263;
x_252 = x_265;
x_253 = x_268;
x_254 = x_267;
x_255 = x_266;
x_256 = x_269;
x_257 = x_270;
x_258 = x_271;
goto block_260;
}
else
{
uint8_t x_272; 
x_272 = lean_unbox(x_218);
x_248 = x_261;
x_249 = x_262;
x_250 = x_264;
x_251 = x_263;
x_252 = x_265;
x_253 = x_268;
x_254 = x_267;
x_255 = x_266;
x_256 = x_269;
x_257 = x_270;
x_258 = x_272;
goto block_260;
}
}
}
block_288:
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; uint8_t x_287; 
x_284 = lean_array_get_size(x_283);
x_285 = lean_unsigned_to_nat(0u);
x_286 = lean_nat_dec_eq(x_284, x_285);
lean_dec(x_284);
x_287 = l_instDecidableNot___redArg(x_286);
if (x_287 == 0)
{
x_261 = x_275;
x_262 = x_274;
x_263 = x_277;
x_264 = x_276;
x_265 = x_278;
x_266 = x_281;
x_267 = x_280;
x_268 = x_279;
x_269 = x_283;
x_270 = x_282;
goto block_273;
}
else
{
if (x_281 == 0)
{
x_261 = x_275;
x_262 = x_274;
x_263 = x_277;
x_264 = x_276;
x_265 = x_278;
x_266 = x_281;
x_267 = x_280;
x_268 = x_279;
x_269 = x_283;
x_270 = x_282;
goto block_273;
}
else
{
x_220 = x_274;
x_221 = x_275;
x_222 = x_277;
x_223 = x_276;
x_224 = x_281;
x_225 = x_280;
x_226 = x_279;
x_227 = x_282;
x_228 = x_283;
goto block_247;
}
}
}
block_303:
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_302; 
x_299 = lean_array_get_size(x_298);
x_300 = lean_unsigned_to_nat(0u);
x_301 = lean_nat_dec_eq(x_299, x_300);
lean_dec(x_299);
x_302 = l_instDecidableNot___redArg(x_301);
if (x_302 == 0)
{
x_274 = x_290;
x_275 = x_289;
x_276 = x_292;
x_277 = x_291;
x_278 = x_293;
x_279 = x_296;
x_280 = x_295;
x_281 = x_294;
x_282 = x_297;
x_283 = x_298;
goto block_288;
}
else
{
if (x_292 == 0)
{
x_274 = x_290;
x_275 = x_289;
x_276 = x_292;
x_277 = x_291;
x_278 = x_293;
x_279 = x_296;
x_280 = x_295;
x_281 = x_294;
x_282 = x_297;
x_283 = x_298;
goto block_288;
}
else
{
x_220 = x_290;
x_221 = x_289;
x_222 = x_291;
x_223 = x_292;
x_224 = x_294;
x_225 = x_295;
x_226 = x_296;
x_227 = x_297;
x_228 = x_298;
goto block_247;
}
}
}
block_315:
{
uint8_t x_314; 
x_314 = l_instDecidableNot___redArg(x_313);
if (x_314 == 0)
{
if (x_38 == 0)
{
lean_dec(x_312);
lean_dec(x_309);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_304;
x_6 = x_311;
goto block_10;
}
else
{
x_289 = x_305;
x_290 = x_304;
x_291 = x_313;
x_292 = x_306;
x_293 = x_307;
x_294 = x_308;
x_295 = x_309;
x_296 = x_310;
x_297 = x_311;
x_298 = x_312;
goto block_303;
}
}
else
{
x_289 = x_305;
x_290 = x_304;
x_291 = x_313;
x_292 = x_306;
x_293 = x_307;
x_294 = x_308;
x_295 = x_309;
x_296 = x_310;
x_297 = x_311;
x_298 = x_312;
goto block_303;
}
}
block_327:
{
if (x_69 == 0)
{
uint8_t x_325; 
x_325 = lean_unbox(x_219);
x_304 = x_323;
x_305 = x_316;
x_306 = x_317;
x_307 = x_318;
x_308 = x_320;
x_309 = x_322;
x_310 = x_319;
x_311 = x_324;
x_312 = x_321;
x_313 = x_325;
goto block_315;
}
else
{
uint8_t x_326; 
x_326 = lean_unbox(x_218);
x_304 = x_323;
x_305 = x_316;
x_306 = x_317;
x_307 = x_318;
x_308 = x_320;
x_309 = x_322;
x_310 = x_319;
x_311 = x_324;
x_312 = x_321;
x_313 = x_326;
goto block_315;
}
}
block_346:
{
uint8_t x_335; 
x_335 = l_instDecidableNot___redArg(x_334);
if (x_335 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_316 = x_328;
x_317 = x_329;
x_318 = x_330;
x_319 = x_332;
x_320 = x_331;
x_321 = x_333;
x_322 = x_2;
x_323 = x_3;
x_324 = x_4;
goto block_327;
}
else
{
uint8_t x_336; 
x_336 = !lean_is_exclusive(x_3);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_3, 5);
lean_dec(x_337);
x_338 = lean_ctor_get(x_3, 4);
lean_dec(x_338);
x_339 = lean_ctor_get(x_3, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_3, 2);
lean_dec(x_340);
x_341 = lean_ctor_get(x_3, 1);
lean_dec(x_341);
x_342 = lean_ctor_get(x_3, 0);
lean_dec(x_342);
lean_inc(x_68);
x_343 = lean_array_push(x_30, x_68);
lean_inc(x_29);
lean_inc(x_28);
lean_ctor_set(x_3, 2, x_343);
x_316 = x_328;
x_317 = x_329;
x_318 = x_330;
x_319 = x_332;
x_320 = x_331;
x_321 = x_333;
x_322 = x_2;
x_323 = x_3;
x_324 = x_4;
goto block_327;
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_3);
lean_inc(x_68);
x_344 = lean_array_push(x_30, x_68);
lean_inc(x_29);
lean_inc(x_28);
x_345 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_345, 0, x_28);
lean_ctor_set(x_345, 1, x_29);
lean_ctor_set(x_345, 2, x_344);
lean_ctor_set(x_345, 3, x_31);
lean_ctor_set(x_345, 4, x_32);
lean_ctor_set(x_345, 5, x_33);
x_316 = x_328;
x_317 = x_329;
x_318 = x_330;
x_319 = x_332;
x_320 = x_331;
x_321 = x_333;
x_322 = x_2;
x_323 = x_345;
x_324 = x_4;
goto block_327;
}
}
}
block_359:
{
lean_object* x_353; lean_object* x_354; uint8_t x_355; uint8_t x_356; 
x_353 = lean_array_get_size(x_351);
x_354 = lean_unsigned_to_nat(0u);
x_355 = lean_nat_dec_eq(x_353, x_354);
lean_dec(x_353);
x_356 = l_instDecidableNot___redArg(x_355);
if (x_356 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_316 = x_347;
x_317 = x_352;
x_318 = x_348;
x_319 = x_350;
x_320 = x_349;
x_321 = x_351;
x_322 = x_2;
x_323 = x_3;
x_324 = x_4;
goto block_327;
}
else
{
if (x_352 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_316 = x_347;
x_317 = x_352;
x_318 = x_348;
x_319 = x_350;
x_320 = x_349;
x_321 = x_351;
x_322 = x_2;
x_323 = x_3;
x_324 = x_4;
goto block_327;
}
else
{
if (x_69 == 0)
{
uint8_t x_357; 
x_357 = lean_unbox(x_219);
x_328 = x_347;
x_329 = x_352;
x_330 = x_348;
x_331 = x_349;
x_332 = x_350;
x_333 = x_351;
x_334 = x_357;
goto block_346;
}
else
{
uint8_t x_358; 
x_358 = lean_unbox(x_218);
x_328 = x_347;
x_329 = x_352;
x_330 = x_348;
x_331 = x_349;
x_332 = x_350;
x_333 = x_351;
x_334 = x_358;
goto block_346;
}
}
}
}
block_369:
{
uint8_t x_365; lean_object* x_366; 
x_365 = l_Lake_ordLogLevel____x40_Lake_Util_Log___hyg_764_(x_36, x_362);
x_366 = lean_box(x_365);
if (lean_obj_tag(x_366) == 2)
{
uint8_t x_367; 
x_367 = lean_unbox(x_219);
x_347 = x_360;
x_348 = x_361;
x_349 = x_364;
x_350 = x_362;
x_351 = x_363;
x_352 = x_367;
goto block_359;
}
else
{
uint8_t x_368; 
lean_dec(x_366);
x_368 = lean_unbox(x_218);
x_347 = x_360;
x_348 = x_361;
x_349 = x_364;
x_350 = x_362;
x_351 = x_363;
x_352 = x_368;
goto block_359;
}
}
block_378:
{
uint8_t x_374; lean_object* x_375; 
x_374 = l_Lake_ordLogLevel____x40_Lake_Util_Log___hyg_764_(x_35, x_371);
x_375 = lean_box(x_374);
if (lean_obj_tag(x_375) == 2)
{
uint8_t x_376; 
x_376 = lean_unbox(x_219);
x_360 = x_370;
x_361 = x_373;
x_362 = x_371;
x_363 = x_372;
x_364 = x_376;
goto block_369;
}
else
{
uint8_t x_377; 
lean_dec(x_375);
x_377 = lean_unbox(x_218);
x_360 = x_370;
x_361 = x_373;
x_362 = x_371;
x_363 = x_372;
x_364 = x_377;
goto block_369;
}
}
block_387:
{
lean_object* x_380; uint8_t x_381; uint8_t x_382; uint8_t x_383; lean_object* x_384; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get_uint8(x_379, sizeof(void*)*2);
lean_dec(x_379);
x_382 = l_Lake_Log_maxLv(x_380);
x_383 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268_(x_37, x_381);
x_384 = lean_box(x_383);
if (lean_obj_tag(x_384) == 2)
{
uint8_t x_385; 
x_385 = lean_unbox(x_219);
x_370 = x_381;
x_371 = x_382;
x_372 = x_380;
x_373 = x_385;
goto block_378;
}
else
{
uint8_t x_386; 
lean_dec(x_384);
x_386 = lean_unbox(x_218);
x_370 = x_381;
x_371 = x_382;
x_372 = x_380;
x_373 = x_386;
goto block_378;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_1, x_10, x_11, x_4, x_12, x_13, x_7, x_8, x_9);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
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
lean_inc(x_19);
x_20 = lean_io_get_task_state(x_19, x_7);
lean_dec(x_19);
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
lean_dec(x_20);
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
lean_dec(x_20);
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
lean_dec(x_20);
lean_inc(x_18);
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
lean_dec(x_20);
lean_inc(x_18);
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
lean_dec(x_20);
lean_inc(x_5);
x_42 = l_Lake_Monitor_reportJob(x_18, x_5, x_6, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
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
lean_dec(x_5);
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
lean_inc(x_3);
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
lean_inc(x_3);
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
lean_inc(x_2);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_18, x_18);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
return x_19;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec(x_19);
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
lean_inc(x_59);
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
lean_inc(x_59);
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
lean_inc(x_2);
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
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_2);
return x_48;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_47, x_47);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_2);
return x_48;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
lean_dec(x_48);
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
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 3);
lean_inc(x_75);
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
lean_inc(x_91);
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
lean_inc(x_91);
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
lean_inc(x_2);
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
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_2);
return x_80;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_79, x_79);
if (x_85 == 0)
{
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_2);
return x_80;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
lean_dec(x_80);
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
lean_inc(x_114);
x_115 = lean_ctor_get(x_3, 3);
lean_inc(x_115);
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
lean_inc(x_131);
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
lean_inc(x_131);
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
lean_inc(x_2);
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
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_105);
lean_dec(x_2);
return x_120;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_119, x_119);
if (x_125 == 0)
{
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_105);
lean_dec(x_2);
return x_120;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
lean_dec(x_120);
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
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec(x_1);
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
lean_dec(x_35);
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
lean_dec(x_45);
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
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 3);
lean_inc(x_27);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec(x_1);
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
lean_dec(x_2);
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
lean_inc(x_2);
x_19 = l_Lake_Monitor_renderProgress___redArg(x_13, x_14, x_2, x_11, x_9);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lake_Monitor_sleep(x_2, x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
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
lean_dec(x_2);
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
lean_inc(x_2);
x_35 = l_Lake_Monitor_renderProgress___redArg(x_28, x_29, x_2, x_11, x_9);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lake_Monitor_sleep(x_2, x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
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
lean_dec(x_2);
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
lean_inc(x_2);
x_55 = l_Lake_Monitor_renderProgress___redArg(x_46, x_47, x_2, x_45, x_44);
lean_dec(x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lake_Monitor_sleep(x_2, x_58, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
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
lean_inc(x_2);
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
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_12);
x_32 = lean_apply_2(x_24, x_12, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_25 = x_33;
goto block_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(x_21);
x_37 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lake_print_x21___closed__2;
x_39 = l_Lake_print_x21___closed__3;
x_40 = lean_unsigned_to_nat(79u);
x_41 = lean_unsigned_to_nat(4u);
x_42 = l_Lake_print_x21___closed__4;
x_43 = l_Lake_print_x21___closed__7;
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_Name_toString(x_43, x_45, x_37);
x_47 = lean_string_append(x_42, x_46);
lean_dec(x_46);
x_48 = l_Lake_print_x21___closed__8;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_io_error_to_string(x_34);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = l_Lake_print_x21___closed__9;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_String_quote(x_12);
lean_dec(x_12);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_unsigned_to_nat(120u);
x_57 = lean_format_pretty(x_55, x_56, x_20, x_20);
x_58 = lean_string_append(x_53, x_57);
lean_dec(x_57);
x_59 = l_mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_58);
lean_dec(x_58);
x_60 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_59, x_35);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_25 = x_61;
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
lean_dec(x_26);
x_14 = x_27;
x_15 = x_28;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_14 = x_30;
x_15 = x_29;
goto block_18;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_9);
return x_64;
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_ctor_get(x_7, 1);
x_67 = lean_ctor_get(x_7, 2);
x_68 = lean_ctor_get(x_7, 3);
x_69 = lean_ctor_get(x_7, 4);
x_70 = lean_ctor_get(x_7, 5);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_7);
x_71 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_67);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_69);
lean_ctor_set(x_72, 5, x_70);
x_78 = lean_string_utf8_byte_size(x_68);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_91; 
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 4);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_68);
x_91 = lean_apply_2(x_83, x_68, x_9);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_dec(x_68);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_84 = x_92;
goto block_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_box(x_80);
x_96 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_96, 0, x_95);
x_97 = l_Lake_print_x21___closed__2;
x_98 = l_Lake_print_x21___closed__3;
x_99 = lean_unsigned_to_nat(79u);
x_100 = lean_unsigned_to_nat(4u);
x_101 = l_Lake_print_x21___closed__4;
x_102 = l_Lake_print_x21___closed__7;
x_103 = lean_box(1);
x_104 = lean_unbox(x_103);
x_105 = l_Lean_Name_toString(x_102, x_104, x_96);
x_106 = lean_string_append(x_101, x_105);
lean_dec(x_105);
x_107 = l_Lake_print_x21___closed__8;
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_io_error_to_string(x_93);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
x_111 = l_Lake_print_x21___closed__9;
x_112 = lean_string_append(x_110, x_111);
x_113 = l_String_quote(x_68);
lean_dec(x_68);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_unsigned_to_nat(120u);
x_116 = lean_format_pretty(x_114, x_115, x_79, x_79);
x_117 = lean_string_append(x_112, x_116);
lean_dec(x_116);
x_118 = l_mkPanicMessageWithDecl(x_97, x_98, x_99, x_100, x_117);
lean_dec(x_117);
x_119 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_118, x_94);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_84 = x_120;
goto block_90;
}
block_90:
{
lean_object* x_85; 
x_85 = lean_apply_1(x_82, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_73 = x_86;
x_74 = x_87;
goto block_77;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_box(0);
x_73 = x_89;
x_74 = x_88;
goto block_77;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_68);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_72);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_9);
return x_123;
}
block_77:
{
lean_object* x_75; lean_object* x_76; 
if (lean_is_scalar(x_8)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_8;
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_72);
if (lean_is_scalar(x_10)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_10;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_main___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Monitor_main___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_io_mono_ms_now(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
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
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Lake_monitorJobs(x_1, x_2, x_3, x_14, x_15, x_16, x_17, x_18, x_19, x_10, x_11, x_12, x_13);
return x_20;
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdout(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdin(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stderr(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_mk_ref(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
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
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
x_20 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(x_19, x_4, x_5, x_6, x_18, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(x_19, x_4, x_5, x_6, x_24, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_7, 0, x_29);
x_30 = l_IO_FS_Stream_ofBuffer(x_23);
lean_inc(x_28);
x_31 = l_IO_FS_Stream_ofBuffer(x_28);
if (x_2 == 0)
{
x_32 = x_1;
goto block_59;
}
else
{
lean_object* x_60; 
lean_inc(x_31);
x_60 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2), 9, 3);
lean_closure_set(x_60, 0, lean_box(0));
lean_closure_set(x_60, 1, x_31);
lean_closure_set(x_60, 2, x_1);
x_32 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0), 9, 3);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_31);
lean_closure_set(x_33, 2, x_32);
x_34 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_30, x_33, x_3, x_4, x_5, x_6, x_7, x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_st_ref_get(x_28, x_36);
lean_dec(x_28);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_string_validate_utf8(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
x_45 = l_panic___at___Lean_Name_getString_x21_spec__0(x_44);
x_9 = x_37;
x_10 = x_41;
x_11 = x_38;
x_12 = x_45;
goto block_16;
}
else
{
lean_object* x_46; 
x_46 = lean_string_from_utf8_unchecked(x_42);
lean_dec(x_42);
x_9 = x_37;
x_10 = x_41;
x_11 = x_38;
x_12 = x_46;
goto block_16;
}
}
else
{
uint8_t x_47; 
lean_dec(x_28);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_34, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_34, 0, x_52);
return x_34;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
lean_dec(x_34);
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_56 = x_35;
} else {
 lean_dec_ref(x_35);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_inc(x_61);
lean_dec(x_7);
x_64 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
x_65 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(x_64, x_4, x_5, x_6, x_61, x_8);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(x_64, x_4, x_5, x_6, x_69, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_63);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_62);
x_76 = l_IO_FS_Stream_ofBuffer(x_68);
lean_inc(x_73);
x_77 = l_IO_FS_Stream_ofBuffer(x_73);
if (x_2 == 0)
{
x_78 = x_1;
goto block_100;
}
else
{
lean_object* x_101; 
lean_inc(x_77);
x_101 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2), 9, 3);
lean_closure_set(x_101, 0, lean_box(0));
lean_closure_set(x_101, 1, x_77);
lean_closure_set(x_101, 2, x_1);
x_78 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0), 9, 3);
lean_closure_set(x_79, 0, lean_box(0));
lean_closure_set(x_79, 1, x_77);
lean_closure_set(x_79, 2, x_78);
x_80 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_76, x_79, x_3, x_4, x_5, x_6, x_75, x_72);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_st_ref_get(x_73, x_82);
lean_dec(x_73);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_string_validate_utf8(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
x_91 = l_panic___at___Lean_Name_getString_x21_spec__0(x_90);
x_9 = x_83;
x_10 = x_87;
x_11 = x_84;
x_12 = x_91;
goto block_16;
}
else
{
lean_object* x_92; 
x_92 = lean_string_from_utf8_unchecked(x_88);
lean_dec(x_88);
x_9 = x_83;
x_10 = x_87;
x_11 = x_84;
x_12 = x_92;
goto block_16;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_73);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_94 = x_80;
} else {
 lean_dec_ref(x_80);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_81, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_97 = x_81;
} else {
 lean_dec_ref(x_81);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
return x_99;
}
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_array_uget(x_3, x_4);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_Monitor_reportJob___closed__0;
x_20 = lean_string_append(x_18, x_19);
lean_inc(x_20);
x_21 = lean_apply_2(x_15, x_20, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_8 = x_22;
x_9 = x_23;
goto block_13;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lake_print_x21___closed__2;
x_27 = l_Lake_print_x21___closed__3;
x_28 = lean_unsigned_to_nat(79u);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lake_print_x21___closed__4;
x_31 = l_Lake_print_x21___closed__7;
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
lean_inc(x_2);
x_34 = l_Lean_Name_toString(x_31, x_33, x_2);
x_35 = lean_string_append(x_30, x_34);
lean_dec(x_34);
x_36 = l_Lake_print_x21___closed__8;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_io_error_to_string(x_24);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lake_print_x21___closed__9;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_String_quote(x_20);
lean_dec(x_20);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_unsigned_to_nat(120u);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_format_pretty(x_43, x_44, x_45, x_45);
x_47 = lean_string_append(x_41, x_46);
lean_dec(x_46);
x_48 = l_mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_47);
lean_dec(x_47);
x_49 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_48, x_25);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_8 = x_50;
x_9 = x_51;
goto block_13;
}
}
else
{
lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_7);
return x_52;
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
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_array_uget(x_3, x_4);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___closed__0;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lake_Monitor_reportJob___closed__0;
x_20 = lean_string_append(x_18, x_19);
lean_inc(x_20);
x_21 = lean_apply_2(x_15, x_20, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_8 = x_22;
x_9 = x_23;
goto block_13;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lake_print_x21___closed__2;
x_27 = l_Lake_print_x21___closed__3;
x_28 = lean_unsigned_to_nat(79u);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lake_print_x21___closed__4;
x_31 = l_Lake_print_x21___closed__7;
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
lean_inc(x_2);
x_34 = l_Lean_Name_toString(x_31, x_33, x_2);
x_35 = lean_string_append(x_30, x_34);
lean_dec(x_34);
x_36 = l_Lake_print_x21___closed__8;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_io_error_to_string(x_24);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lake_print_x21___closed__9;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_String_quote(x_20);
lean_dec(x_20);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_unsigned_to_nat(120u);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_format_pretty(x_43, x_44, x_45, x_45);
x_47 = lean_string_append(x_41, x_46);
lean_dec(x_46);
x_48 = l_mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_47);
lean_dec(x_47);
x_49 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_48, x_25);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_8 = x_50;
x_9 = x_51;
goto block_13;
}
}
else
{
lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_7);
return x_52;
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_6, 0, x_15);
lean_ctor_set(x_11, 1, x_6);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_22 = x_11;
} else {
 lean_dec_ref(x_11);
 x_22 = lean_box(0);
}
lean_ctor_set(x_6, 0, x_21);
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_11, 1, x_6);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_35 = x_11;
} else {
 lean_dec_ref(x_11);
 x_35 = lean_box(0);
}
lean_ctor_set(x_6, 0, x_34);
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_6);
x_41 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_38, x_7);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_39);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_44)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_44;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_55 = x_42;
} else {
 lean_dec_ref(x_42);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_39);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_recFetch___at___Lake_recFetchAcyclic___at___Lake_recFetchWithIndex_spec__0_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_16 = x_11;
} else {
 lean_dec_ref(x_11);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_24 = lean_string_utf8_byte_size(x_17);
x_25 = lean_nat_dec_eq(x_24, x_8);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
x_29 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_30 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_29, x_24);
x_31 = lean_string_utf8_extract(x_17, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_17);
x_32 = lean_string_append(x_28, x_31);
lean_dec(x_31);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_array_push(x_27, x_34);
lean_ctor_set(x_15, 0, x_36);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_15);
x_40 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
x_41 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_42 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_41, x_24);
x_43 = lean_string_utf8_extract(x_17, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_17);
x_44 = lean_string_append(x_40, x_43);
lean_dec(x_43);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
x_48 = lean_array_push(x_37, x_46);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_38);
x_19 = x_49;
x_20 = x_13;
goto block_23;
}
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_8);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_10, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_10;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_10, 0, x_55);
return x_10;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_59 = x_11;
} else {
 lean_dec_ref(x_11);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__4;
x_2 = lean_box(0);
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__2;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("job computation", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Some required builds logged failures:\n", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__8;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(120u);
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__10;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("top-level build failed", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__12;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_14 = l_Lake_OutStream_get(x_12, x_4);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_22 = l_Lake_AnsiMode_isEnabled(x_15, x_13, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
x_25 = l_Lake_mkBuildContext(x_1, x_3, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_st_mk_ref(x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__0), 7, 1);
lean_closure_set(x_32, 0, x_2);
x_33 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__1), 6, 0);
x_34 = lean_unsigned_to_nat(0u);
x_51 = lean_box(0);
x_52 = l_Lake_Workspace_runFetchM___redArg___closed__2;
x_53 = lean_box(0);
x_54 = l_Lake_Workspace_runFetchM___redArg___closed__5;
x_55 = lean_box(1);
lean_inc(x_26);
lean_inc(x_30);
x_56 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__2___boxed), 9, 8);
lean_closure_set(x_56, 0, x_32);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_33);
lean_closure_set(x_56, 3, x_51);
lean_closure_set(x_56, 4, x_30);
lean_closure_set(x_56, 5, x_26);
lean_closure_set(x_56, 6, x_54);
lean_closure_set(x_56, 7, x_34);
x_57 = lean_io_as_task(x_56, x_34, x_31);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_30, x_59);
lean_dec(x_30);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = l_Lake_BuildConfig_showProgress(x_3);
lean_dec(x_3);
x_64 = l_Lake_Workspace_runFetchM___redArg___closed__6;
x_65 = lean_box(0);
lean_inc(x_58);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_64);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_67);
x_68 = lean_box(2);
x_69 = lean_unbox(x_68);
x_70 = l_Lake_instDecidableEqVerbosity(x_9, x_69);
if (x_70 == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_box(2);
x_127 = lean_unbox(x_126);
x_71 = x_127;
goto block_125;
}
else
{
uint8_t x_128; 
x_128 = lean_unbox(x_53);
x_71 = x_128;
goto block_125;
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
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_apply_1(x_18, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_5 = x_20;
goto block_8;
}
block_50:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_array_get_size(x_36);
x_39 = lean_nat_dec_lt(x_34, x_38);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
x_17 = x_37;
goto block_21;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_38, x_38);
if (x_40 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
x_17 = x_37;
goto block_21;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_box(0);
x_42 = 0;
x_43 = lean_usize_of_nat(x_38);
lean_dec(x_38);
lean_inc(x_15);
x_44 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(x_15, x_35, x_36, x_42, x_43, x_41, x_37);
lean_dec(x_36);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_17 = x_45;
goto block_21;
}
else
{
uint8_t x_46; 
lean_dec(x_15);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
block_125:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_72 = lean_ctor_get(x_26, 3);
lean_inc(x_72);
lean_dec(x_26);
x_73 = l_Lake_Job_toOpaque___redArg(x_66);
x_74 = l_Lake_Workspace_runFetchM___redArg___closed__7;
x_75 = lean_array_push(x_74, x_73);
x_76 = l_Lake_Monitor_renderProgress___redArg___closed__1;
x_77 = lean_unsigned_to_nat(100u);
x_78 = lean_unbox(x_23);
lean_dec(x_23);
lean_inc(x_15);
x_79 = l_Lake_monitorJobs(x_75, x_72, x_15, x_10, x_11, x_71, x_70, x_78, x_63, x_76, x_52, x_77, x_61);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Array_isEmpty___redArg(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_58);
x_83 = lean_ctor_get(x_15, 4);
lean_inc(x_83);
x_84 = lean_box(x_82);
x_85 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_85, 0, x_84);
x_86 = l_Lake_Workspace_runFetchM___redArg___closed__8;
x_87 = lean_apply_2(x_83, x_86, x_81);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_35 = x_85;
x_36 = x_80;
x_37 = x_88;
goto block_50;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Lake_print_x21___closed__2;
x_92 = l_Lake_print_x21___closed__3;
x_93 = lean_unsigned_to_nat(79u);
x_94 = lean_unsigned_to_nat(4u);
x_95 = l_Lake_print_x21___closed__4;
x_96 = l_Lake_print_x21___closed__7;
x_97 = lean_unbox(x_55);
lean_inc(x_85);
x_98 = l_Lean_Name_toString(x_96, x_97, x_85);
x_99 = lean_string_append(x_95, x_98);
lean_dec(x_98);
x_100 = l_Lake_print_x21___closed__8;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_io_error_to_string(x_89);
x_103 = lean_string_append(x_101, x_102);
lean_dec(x_102);
x_104 = l_Lake_print_x21___closed__9;
x_105 = lean_string_append(x_103, x_104);
x_106 = l_Lake_Workspace_runFetchM___redArg___closed__11;
x_107 = lean_string_append(x_105, x_106);
x_108 = l_mkPanicMessageWithDecl(x_91, x_92, x_93, x_94, x_107);
lean_dec(x_107);
x_109 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_108, x_90);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_35 = x_85;
x_36 = x_80;
x_37 = x_110;
goto block_50;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_80);
lean_dec(x_15);
x_111 = lean_io_wait(x_58, x_81);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
lean_ctor_set(x_111, 0, x_115);
return x_111;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_dec(x_112);
x_119 = !lean_is_exclusive(x_111);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_111, 0);
lean_dec(x_120);
x_121 = l_Lake_Workspace_runFetchM___redArg___closed__13;
lean_ctor_set_tag(x_111, 1);
lean_ctor_set(x_111, 0, x_121);
return x_111;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_111, 1);
lean_inc(x_122);
lean_dec(x_111);
x_123 = l_Lake_Workspace_runFetchM___redArg___closed__13;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_dec(x_3);
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
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Workspace_runFetchM___redArg___lam__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
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
lean_dec(x_10);
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
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
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
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
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
uint8_t x_18; 
lean_dec(x_11);
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
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
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
lean_dec(x_10);
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
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
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
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
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
uint8_t x_18; 
lean_dec(x_11);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
