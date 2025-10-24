// Lean compiler output
// Module: Lake.Build.Run
// Imports: public import Lake.Config.Workspace import Lake.Config.Monad import Lake.Build.Job.Monad import Lake.Build.Index
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
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx___boxed(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__13;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7;
uint8_t l_Lake_instDecidableEqJobAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8;
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*);
static uint64_t l_Lake_mkBuildContext___closed__1;
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__13;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
uint8_t l_Lake_instOrdJobAction_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
static lean_object* l_Lake_mkBuildContext___closed__2;
lean_object* l_instMonadST(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__17;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4;
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__4;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__6;
static lean_object* l_Lake_mkBuildContext___closed__7;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
uint8_t lean_strict_and(uint8_t, uint8_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__6;
lean_object* l_Lake_OutStream_get(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__16;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__5;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__19;
lean_object* lean_io_mono_ms_now();
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2;
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6;
static lean_object* l_Lake_mkBuildContext___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__10;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5;
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__14;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__0;
lean_object* l_IO_sleep(uint32_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__11;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__6;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__9;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__18;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__7;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__12;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1;
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__5;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__12;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__4;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_mkBuildContext___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__9;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__13;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__9;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_Env_leanGithash(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__8;
lean_object* lean_io_exit(uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
extern lean_object* l_Lean_versionStringCore;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9_spec__9(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__15;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__10;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
static uint8_t l_Lake_Workspace_runFetchM___redArg___lam__2___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorResult_ctorIdx(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
lean_object* lean_io_wait(lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__4;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1;
static lean_object* l_Lake_mkBuildContext___closed__8;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__10;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__5;
static lean_object* _init_l_Lake_mkBuildContext___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_mkBuildContext___closed__1() {
_start:
{
uint64_t x_1; 
x_1 = l_Lake_Hash_nil;
return x_1;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_versionStringCore;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", commit ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mkBuildContext___closed__5;
x_2 = l_Lake_mkBuildContext___closed__4;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__8() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_mkBuildContext___closed__7;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lake_mkBuildContext___closed__0;
x_5 = lean_st_mk_ref(x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lake_Env_leanGithash(x_6);
x_8 = l_Lake_mkBuildContext___closed__1;
x_9 = lean_string_hash(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lake_mkBuildContext___closed__6;
x_12 = lean_string_append(x_11, x_7);
lean_dec_ref(x_7);
x_13 = l_Lake_mkBuildContext___closed__8;
x_14 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint64(x_14, sizeof(void*)*3, x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkBuildContext(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10494;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10487;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10479;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10463;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10367;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10431;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10491;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10493;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_3, x_1, x_2, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_4, x_2, x_3, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_MonitorM_run(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\x1b[2K\r", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Ansi_resetLine() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_4);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Run_0__Lake_flush(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
x_3 = l_instInhabitedOfMonad___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lake.Build.Run.0.Lake.print!", 37, 37);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__5;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__6;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Build", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__9;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__8;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Run", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__11;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__10;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__13;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("print!", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__14;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" failed: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_5 = lean_apply_2(x_4, x_2, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_10 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_11 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_12 = lean_unsigned_to_nat(84u);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_16 = lean_io_error_to_string(x_8);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_String_quote(x_2);
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 0, x_20);
x_21 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_22 = l_Std_Format_pretty(x_5, x_21, x_14, x_14);
x_23 = lean_string_append(x_19, x_22);
lean_dec_ref(x_22);
x_24 = l_mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_23);
lean_dec_ref(x_23);
x_25 = l_panic___redArg(x_9, x_24);
x_26 = lean_apply_1(x_25, lean_box(0));
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_29 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_30 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_31 = lean_unsigned_to_nat(84u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_35 = lean_io_error_to_string(x_27);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_String_quote(x_2);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_42 = l_Std_Format_pretty(x_40, x_41, x_33, x_33);
x_43 = lean_string_append(x_38, x_42);
lean_dec_ref(x_42);
x_44 = l_mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_43);
lean_dec_ref(x_43);
x_45 = l_panic___redArg(x_28, x_44);
x_46 = lean_apply_1(x_45, lean_box(0));
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_print_x21(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_1);
x_11 = lean_apply_2(x_10, x_1, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_5 = x_12;
x_6 = lean_box(0);
goto block_8;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_16 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_17 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_18 = lean_unsigned_to_nat(84u);
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_22 = lean_io_error_to_string(x_14);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_String_quote(x_1);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_26);
x_27 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_28 = l_Std_Format_pretty(x_11, x_27, x_20, x_20);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = l_mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_29);
lean_dec_ref(x_29);
x_31 = l_panic___redArg(x_15, x_30);
x_32 = lean_apply_1(x_31, lean_box(0));
x_5 = x_32;
x_6 = lean_box(0);
goto block_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
x_34 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_35 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_36 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_37 = lean_unsigned_to_nat(84u);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_41 = lean_io_error_to_string(x_33);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_String_quote(x_1);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_48 = l_Std_Format_pretty(x_46, x_47, x_39, x_39);
x_49 = lean_string_append(x_44, x_48);
lean_dec_ref(x_48);
x_50 = l_mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_49);
lean_dec_ref(x_49);
x_51 = l_panic___redArg(x_34, x_50);
x_52 = lean_apply_1(x_51, lean_box(0));
x_5 = x_52;
x_6 = lean_box(0);
goto block_8;
}
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_print(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_1(x_9, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_4 = x_11;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_4 = x_12;
x_5 = lean_box(0);
goto block_7;
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_Monitor_flush(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" [", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Running ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (+ ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" more)", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 5);
if (x_9 == 0)
{
lean_dec_ref(x_3);
goto block_8;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
if (x_10 == 0)
{
lean_dec_ref(x_3);
goto block_8;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; lean_object* x_34; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 5);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_18 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
x_19 = lean_array_fget(x_17, x_15);
x_20 = lean_unbox_uint32(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Fin_add(x_18, x_15, x_21);
lean_dec(x_15);
x_23 = l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_4, 5, x_22);
lean_ctor_set(x_4, 3, x_23);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_array_get_size(x_1);
x_98 = lean_nat_dec_lt(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_97);
x_99 = lean_array_get_size(x_2);
x_100 = lean_nat_sub(x_99, x_21);
lean_dec(x_99);
x_101 = lean_array_fget_borrowed(x_2, x_100);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 2);
x_103 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_104 = lean_string_append(x_103, x_102);
x_34 = x_104;
goto block_95;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_nat_sub(x_97, x_21);
lean_dec(x_97);
x_106 = lean_array_fget_borrowed(x_1, x_105);
x_107 = lean_ctor_get(x_106, 2);
x_108 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_109 = lean_string_append(x_108, x_107);
x_110 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
x_111 = lean_string_append(x_109, x_110);
x_112 = l_Nat_reprFast(x_105);
x_113 = lean_string_append(x_111, x_112);
lean_dec_ref(x_112);
x_114 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
x_115 = lean_string_append(x_113, x_114);
x_34 = x_115;
goto block_95;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
block_33:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_16);
x_30 = lean_apply_1(x_29, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_24 = x_31;
x_25 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_32; 
lean_dec_ref(x_30);
x_32 = lean_box(0);
x_24 = x_32;
x_25 = lean_box(0);
goto block_27;
}
}
block_95:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_16, 4);
x_36 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_37 = lean_string_push(x_36, x_20);
x_38 = lean_string_append(x_14, x_37);
lean_dec_ref(x_37);
x_39 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Nat_reprFast(x_12);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Nat_reprFast(x_13);
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_34);
lean_dec_ref(x_34);
lean_inc_ref(x_35);
lean_inc_ref(x_49);
x_50 = lean_apply_2(x_35, x_49, lean_box(0));
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_28 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_54 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_55 = lean_unsigned_to_nat(84u);
x_56 = lean_unsigned_to_nat(4u);
x_57 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_58 = lean_unsigned_to_nat(0u);
x_59 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_60 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_59, x_10);
x_61 = lean_string_append(x_57, x_60);
lean_dec_ref(x_60);
x_62 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_io_error_to_string(x_52);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = lean_string_append(x_65, x_47);
x_67 = l_String_quote(x_49);
lean_ctor_set_tag(x_50, 3);
lean_ctor_set(x_50, 0, x_67);
x_68 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_69 = l_Std_Format_pretty(x_50, x_68, x_58, x_58);
x_70 = lean_string_append(x_66, x_69);
lean_dec_ref(x_69);
x_71 = l_mkPanicMessageWithDecl(x_53, x_54, x_55, x_56, x_70);
lean_dec_ref(x_70);
x_72 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_71);
x_28 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_73 = lean_ctor_get(x_50, 0);
lean_inc(x_73);
lean_dec(x_50);
x_74 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_75 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_76 = lean_unsigned_to_nat(84u);
x_77 = lean_unsigned_to_nat(4u);
x_78 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_79 = lean_unsigned_to_nat(0u);
x_80 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_81 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_80, x_10);
x_82 = lean_string_append(x_78, x_81);
lean_dec_ref(x_81);
x_83 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_io_error_to_string(x_73);
x_86 = lean_string_append(x_84, x_85);
lean_dec_ref(x_85);
x_87 = lean_string_append(x_86, x_47);
x_88 = l_String_quote(x_49);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_91 = l_Std_Format_pretty(x_89, x_90, x_79, x_79);
x_92 = lean_string_append(x_87, x_91);
lean_dec_ref(x_91);
x_93 = l_mkPanicMessageWithDecl(x_74, x_75, x_76, x_77, x_92);
lean_dec_ref(x_92);
x_94 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_93);
x_28 = lean_box(0);
goto block_33;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_136; lean_object* x_142; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_116 = lean_ctor_get(x_4, 0);
x_117 = lean_ctor_get(x_4, 1);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_119 = lean_ctor_get(x_4, 2);
x_120 = lean_ctor_get(x_4, 3);
x_121 = lean_ctor_get(x_4, 4);
x_122 = lean_ctor_get(x_4, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_4);
x_123 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_123);
lean_dec_ref(x_3);
x_124 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_125 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
x_126 = lean_array_fget(x_124, x_122);
x_127 = lean_unbox_uint32(x_126);
lean_dec(x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = l_Fin_add(x_125, x_122, x_128);
lean_dec(x_122);
x_130 = l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
lean_inc(x_117);
lean_inc(x_116);
x_131 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_117);
lean_ctor_set(x_131, 2, x_119);
lean_ctor_set(x_131, 3, x_130);
lean_ctor_set(x_131, 4, x_121);
lean_ctor_set(x_131, 5, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*6, x_118);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_array_get_size(x_1);
x_185 = lean_nat_dec_lt(x_183, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_184);
x_186 = lean_array_get_size(x_2);
x_187 = lean_nat_sub(x_186, x_128);
lean_dec(x_186);
x_188 = lean_array_fget_borrowed(x_2, x_187);
lean_dec(x_187);
x_189 = lean_ctor_get(x_188, 2);
x_190 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_191 = lean_string_append(x_190, x_189);
x_142 = x_191;
goto block_182;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_192 = lean_nat_sub(x_184, x_128);
lean_dec(x_184);
x_193 = lean_array_fget_borrowed(x_1, x_192);
x_194 = lean_ctor_get(x_193, 2);
x_195 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_196 = lean_string_append(x_195, x_194);
x_197 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
x_198 = lean_string_append(x_196, x_197);
x_199 = l_Nat_reprFast(x_192);
x_200 = lean_string_append(x_198, x_199);
lean_dec_ref(x_199);
x_201 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
x_202 = lean_string_append(x_200, x_201);
x_142 = x_202;
goto block_182;
}
block_135:
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
block_141:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_137);
lean_dec_ref(x_123);
x_138 = lean_apply_1(x_137, lean_box(0));
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_132 = x_139;
x_133 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_140; 
lean_dec_ref(x_138);
x_140 = lean_box(0);
x_132 = x_140;
x_133 = lean_box(0);
goto block_135;
}
}
block_182:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_143 = lean_ctor_get(x_123, 4);
x_144 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_145 = lean_string_push(x_144, x_127);
x_146 = lean_string_append(x_120, x_145);
lean_dec_ref(x_145);
x_147 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
x_148 = lean_string_append(x_146, x_147);
x_149 = l_Nat_reprFast(x_116);
x_150 = lean_string_append(x_148, x_149);
lean_dec_ref(x_149);
x_151 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
x_152 = lean_string_append(x_150, x_151);
x_153 = l_Nat_reprFast(x_117);
x_154 = lean_string_append(x_152, x_153);
lean_dec_ref(x_153);
x_155 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_156 = lean_string_append(x_154, x_155);
x_157 = lean_string_append(x_156, x_142);
lean_dec_ref(x_142);
lean_inc_ref(x_143);
lean_inc_ref(x_157);
x_158 = lean_apply_2(x_143, x_157, lean_box(0));
if (lean_obj_tag(x_158) == 0)
{
lean_dec_ref(x_158);
lean_dec_ref(x_157);
x_136 = lean_box(0);
goto block_141;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
x_161 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_162 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_163 = lean_unsigned_to_nat(84u);
x_164 = lean_unsigned_to_nat(4u);
x_165 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_166 = lean_unsigned_to_nat(0u);
x_167 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_168 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_167, x_10);
x_169 = lean_string_append(x_165, x_168);
lean_dec_ref(x_168);
x_170 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_171 = lean_string_append(x_169, x_170);
x_172 = lean_io_error_to_string(x_159);
x_173 = lean_string_append(x_171, x_172);
lean_dec_ref(x_172);
x_174 = lean_string_append(x_173, x_155);
x_175 = l_String_quote(x_157);
if (lean_is_scalar(x_160)) {
 x_176 = lean_alloc_ctor(3, 1, 0);
} else {
 x_176 = x_160;
 lean_ctor_set_tag(x_176, 3);
}
lean_ctor_set(x_176, 0, x_175);
x_177 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_178 = l_Std_Format_pretty(x_176, x_177, x_166, x_166);
x_179 = lean_string_append(x_174, x_178);
lean_dec_ref(x_178);
x_180 = l_mkPanicMessageWithDecl(x_161, x_162, x_163, x_164, x_179);
lean_dec_ref(x_179);
x_181 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_180);
x_136 = lean_box(0);
goto block_141;
}
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_1, x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ms", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("s", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(10000u);
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Nat_reprFast(x_1);
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_nat_div(x_1, x_4);
x_10 = l_Nat_reprFast(x_9);
x_11 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_unsigned_to_nat(50u);
x_14 = lean_nat_add(x_1, x_13);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(100u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(10u);
x_18 = lean_nat_mod(x_16, x_17);
lean_dec(x_16);
x_19 = l_Nat_reprFast(x_18);
x_20 = lean_string_append(x_12, x_19);
lean_dec_ref(x_19);
x_21 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2;
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_unsigned_to_nat(1000u);
x_24 = lean_nat_div(x_1, x_23);
lean_dec(x_1);
x_25 = l_Nat_reprFast(x_24);
x_26 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2;
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_5, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_12 = l_Lake_logToStream(x_11, x_1, x_2, x_3);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_5, x_13);
x_5 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("32", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (Optional)", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; uint32_t x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_233; lean_object* x_234; uint8_t x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; uint32_t x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_248; uint8_t x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; uint32_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint32_t x_281; lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; uint8_t x_296; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; uint8_t x_313; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; uint8_t x_320; uint8_t x_321; lean_object* x_322; uint8_t x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; uint8_t x_345; uint8_t x_346; uint8_t x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; uint8_t x_366; uint8_t x_367; lean_object* x_368; uint8_t x_369; uint8_t x_370; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_379; lean_object* x_380; uint8_t x_381; uint8_t x_382; lean_object* x_388; lean_object* x_401; lean_object* x_402; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_ctor_get(x_3, 4);
x_30 = lean_ctor_get(x_3, 5);
x_31 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_194 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_195);
x_196 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_401 = lean_task_get_own(x_194);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec_ref(x_401);
x_388 = x_402;
goto block_400;
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_apply_1(x_19, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_10 = x_16;
x_11 = x_21;
x_12 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_10 = x_16;
x_11 = x_22;
x_12 = lean_box(0);
goto block_14;
}
}
block_53:
{
uint8_t x_46; 
x_46 = lean_nat_dec_lt(x_43, x_40);
lean_dec(x_43);
if (x_46 == 0)
{
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_31);
x_15 = x_44;
x_16 = x_42;
x_17 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_40, x_40);
if (x_47 == 0)
{
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_31);
x_15 = x_44;
x_16 = x_42;
x_17 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_31, x_45, x_36, x_39, x_49, x_50, x_48, x_42);
lean_dec_ref(x_39);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_15 = x_44;
x_16 = x_52;
x_17 = lean_box(0);
goto block_23;
}
}
}
block_63:
{
if (x_55 == 0)
{
lean_dec(x_59);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec_ref(x_31);
x_15 = x_60;
x_16 = x_58;
x_17 = lean_box(0);
goto block_23;
}
else
{
if (x_57 == 0)
{
x_39 = x_54;
x_40 = x_56;
x_41 = lean_box(0);
x_42 = x_58;
x_43 = x_59;
x_44 = x_60;
x_45 = x_32;
goto block_53;
}
else
{
uint8_t x_62; 
x_62 = 0;
x_39 = x_54;
x_40 = x_56;
x_41 = lean_box(0);
x_42 = x_58;
x_43 = x_59;
x_44 = x_60;
x_45 = x_62;
goto block_53;
}
}
}
block_180:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_72, 1);
x_76 = lean_ctor_get(x_70, 3);
x_77 = lean_ctor_get(x_75, 4);
x_78 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
lean_ctor_set(x_70, 3, x_78);
x_79 = lean_string_append(x_76, x_73);
lean_dec_ref(x_73);
x_80 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
x_81 = lean_string_append(x_79, x_80);
lean_inc_ref(x_77);
lean_inc_ref(x_81);
x_82 = lean_apply_2(x_77, x_81, lean_box(0));
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_82);
lean_dec_ref(x_81);
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
x_57 = x_67;
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_86 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_87 = lean_unsigned_to_nat(84u);
x_88 = lean_unsigned_to_nat(4u);
x_89 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_90 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_91 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_71);
x_92 = l_Lean_Name_num___override(x_91, x_71);
x_93 = l_Lean_Name_str___override(x_92, x_90);
x_94 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_95 = l_Lean_Name_str___override(x_93, x_94);
x_96 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_95, x_69);
x_97 = lean_string_append(x_89, x_96);
lean_dec_ref(x_96);
x_98 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_io_error_to_string(x_84);
x_101 = lean_string_append(x_99, x_100);
lean_dec_ref(x_100);
x_102 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_103 = lean_string_append(x_101, x_102);
x_104 = l_String_quote(x_81);
lean_ctor_set_tag(x_82, 3);
lean_ctor_set(x_82, 0, x_104);
x_105 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc_n(x_71, 2);
x_106 = l_Std_Format_pretty(x_82, x_105, x_71, x_71);
x_107 = lean_string_append(x_103, x_106);
lean_dec_ref(x_106);
x_108 = l_mkPanicMessageWithDecl(x_85, x_86, x_87, x_88, x_107);
lean_dec_ref(x_107);
x_109 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_108);
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
x_57 = x_67;
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_110 = lean_ctor_get(x_82, 0);
lean_inc(x_110);
lean_dec(x_82);
x_111 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_112 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_113 = lean_unsigned_to_nat(84u);
x_114 = lean_unsigned_to_nat(4u);
x_115 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_116 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_117 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_71);
x_118 = l_Lean_Name_num___override(x_117, x_71);
x_119 = l_Lean_Name_str___override(x_118, x_116);
x_120 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_121 = l_Lean_Name_str___override(x_119, x_120);
x_122 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_121, x_69);
x_123 = lean_string_append(x_115, x_122);
lean_dec_ref(x_122);
x_124 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_io_error_to_string(x_110);
x_127 = lean_string_append(x_125, x_126);
lean_dec_ref(x_126);
x_128 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_129 = lean_string_append(x_127, x_128);
x_130 = l_String_quote(x_81);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc_n(x_71, 2);
x_133 = l_Std_Format_pretty(x_131, x_132, x_71, x_71);
x_134 = lean_string_append(x_129, x_133);
lean_dec_ref(x_133);
x_135 = l_mkPanicMessageWithDecl(x_111, x_112, x_113, x_114, x_134);
lean_dec_ref(x_134);
x_136 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_135);
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
x_57 = x_67;
x_58 = x_70;
x_59 = x_71;
x_60 = x_72;
x_61 = lean_box(0);
goto block_63;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_137 = lean_ctor_get(x_72, 1);
x_138 = lean_ctor_get(x_70, 0);
x_139 = lean_ctor_get(x_70, 1);
x_140 = lean_ctor_get_uint8(x_70, sizeof(void*)*6);
x_141 = lean_ctor_get(x_70, 2);
x_142 = lean_ctor_get(x_70, 3);
x_143 = lean_ctor_get(x_70, 4);
x_144 = lean_ctor_get(x_70, 5);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_70);
x_145 = lean_ctor_get(x_137, 4);
x_146 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_147 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_147, 0, x_138);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_141);
lean_ctor_set(x_147, 3, x_146);
lean_ctor_set(x_147, 4, x_143);
lean_ctor_set(x_147, 5, x_144);
lean_ctor_set_uint8(x_147, sizeof(void*)*6, x_140);
x_148 = lean_string_append(x_142, x_73);
lean_dec_ref(x_73);
x_149 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
x_150 = lean_string_append(x_148, x_149);
lean_inc_ref(x_145);
lean_inc_ref(x_150);
x_151 = lean_apply_2(x_145, x_150, lean_box(0));
if (lean_obj_tag(x_151) == 0)
{
lean_dec_ref(x_151);
lean_dec_ref(x_150);
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
x_57 = x_67;
x_58 = x_147;
x_59 = x_71;
x_60 = x_72;
x_61 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_155 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_156 = lean_unsigned_to_nat(84u);
x_157 = lean_unsigned_to_nat(4u);
x_158 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_159 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_160 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_71);
x_161 = l_Lean_Name_num___override(x_160, x_71);
x_162 = l_Lean_Name_str___override(x_161, x_159);
x_163 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_164 = l_Lean_Name_str___override(x_162, x_163);
x_165 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_164, x_69);
x_166 = lean_string_append(x_158, x_165);
lean_dec_ref(x_165);
x_167 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_io_error_to_string(x_152);
x_170 = lean_string_append(x_168, x_169);
lean_dec_ref(x_169);
x_171 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_172 = lean_string_append(x_170, x_171);
x_173 = l_String_quote(x_150);
if (lean_is_scalar(x_153)) {
 x_174 = lean_alloc_ctor(3, 1, 0);
} else {
 x_174 = x_153;
 lean_ctor_set_tag(x_174, 3);
}
lean_ctor_set(x_174, 0, x_173);
x_175 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc_n(x_71, 2);
x_176 = l_Std_Format_pretty(x_174, x_175, x_71, x_71);
x_177 = lean_string_append(x_172, x_176);
lean_dec_ref(x_176);
x_178 = l_mkPanicMessageWithDecl(x_154, x_155, x_156, x_157, x_177);
lean_dec_ref(x_177);
x_179 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_178);
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
x_57 = x_67;
x_58 = x_147;
x_59 = x_71;
x_60 = x_72;
x_61 = lean_box(0);
goto block_63;
}
}
}
block_193:
{
lean_object* x_192; 
x_192 = l_Lake_Ansi_chalk(x_191, x_184);
lean_dec_ref(x_184);
lean_dec_ref(x_191);
x_64 = x_181;
x_65 = x_183;
x_66 = x_182;
x_67 = x_185;
x_68 = lean_box(0);
x_69 = x_188;
x_70 = x_187;
x_71 = x_189;
x_72 = x_190;
x_73 = x_192;
goto block_180;
}
block_232:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_211 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_212 = lean_string_push(x_211, x_203);
x_213 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
x_214 = lean_string_append(x_212, x_213);
x_215 = l_Nat_reprFast(x_24);
x_216 = lean_string_append(x_214, x_215);
lean_dec_ref(x_215);
x_217 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
x_218 = lean_string_append(x_216, x_217);
x_219 = l_Nat_reprFast(x_25);
x_220 = lean_string_append(x_218, x_219);
lean_dec_ref(x_219);
x_221 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1;
x_222 = lean_string_append(x_220, x_221);
x_223 = lean_string_append(x_222, x_197);
lean_dec_ref(x_197);
x_224 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2;
x_225 = lean_string_append(x_223, x_224);
x_226 = lean_string_append(x_225, x_201);
lean_dec_ref(x_201);
x_227 = lean_string_append(x_226, x_224);
x_228 = lean_string_append(x_227, x_195);
lean_dec_ref(x_195);
x_229 = lean_string_append(x_228, x_210);
lean_dec_ref(x_210);
if (x_36 == 0)
{
x_64 = x_198;
x_65 = x_205;
x_66 = x_199;
x_67 = x_200;
x_68 = lean_box(0);
x_69 = x_208;
x_70 = x_207;
x_71 = x_204;
x_72 = x_209;
x_73 = x_229;
goto block_180;
}
else
{
if (x_199 == 0)
{
lean_object* x_230; 
x_230 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3;
x_181 = x_198;
x_182 = x_199;
x_183 = x_205;
x_184 = x_229;
x_185 = x_200;
x_186 = lean_box(0);
x_187 = x_207;
x_188 = x_208;
x_189 = x_204;
x_190 = x_209;
x_191 = x_230;
goto block_193;
}
else
{
lean_object* x_231; 
x_231 = l_Lake_LogLevel_ansiColor(x_206);
x_181 = x_198;
x_182 = x_199;
x_183 = x_205;
x_184 = x_229;
x_185 = x_200;
x_186 = lean_box(0);
x_187 = x_207;
x_188 = x_208;
x_189 = x_204;
x_190 = x_209;
x_191 = x_231;
goto block_193;
}
}
}
block_247:
{
lean_object* x_246; 
x_246 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_197 = x_233;
x_198 = x_234;
x_199 = x_235;
x_200 = x_236;
x_201 = x_237;
x_202 = lean_box(0);
x_203 = x_239;
x_204 = x_240;
x_205 = x_241;
x_206 = x_242;
x_207 = x_243;
x_208 = x_244;
x_209 = x_245;
x_210 = x_246;
goto block_232;
}
block_268:
{
if (x_38 == 0)
{
lean_dec(x_256);
x_233 = x_261;
x_234 = x_248;
x_235 = x_249;
x_236 = x_250;
x_237 = x_251;
x_238 = lean_box(0);
x_239 = x_253;
x_240 = x_254;
x_241 = x_255;
x_242 = x_257;
x_243 = x_258;
x_244 = x_259;
x_245 = x_260;
goto block_247;
}
else
{
uint8_t x_262; 
x_262 = lean_nat_dec_lt(x_254, x_256);
if (x_262 == 0)
{
lean_dec(x_256);
x_233 = x_261;
x_234 = x_248;
x_235 = x_249;
x_236 = x_250;
x_237 = x_251;
x_238 = lean_box(0);
x_239 = x_253;
x_240 = x_254;
x_241 = x_255;
x_242 = x_257;
x_243 = x_258;
x_244 = x_259;
x_245 = x_260;
goto block_247;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4;
x_264 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(x_256);
x_265 = lean_string_append(x_263, x_264);
lean_dec_ref(x_264);
x_266 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5;
x_267 = lean_string_append(x_265, x_266);
x_197 = x_261;
x_198 = x_248;
x_199 = x_249;
x_200 = x_250;
x_201 = x_251;
x_202 = lean_box(0);
x_203 = x_253;
x_204 = x_254;
x_205 = x_255;
x_206 = x_257;
x_207 = x_258;
x_208 = x_259;
x_209 = x_260;
x_210 = x_267;
goto block_232;
}
}
}
block_284:
{
if (x_196 == 0)
{
lean_object* x_282; 
x_282 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_248 = x_269;
x_249 = x_271;
x_250 = x_273;
x_251 = x_275;
x_252 = lean_box(0);
x_253 = x_281;
x_254 = x_279;
x_255 = x_270;
x_256 = x_272;
x_257 = x_276;
x_258 = x_278;
x_259 = x_277;
x_260 = x_280;
x_261 = x_282;
goto block_268;
}
else
{
lean_object* x_283; 
x_283 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6;
x_248 = x_269;
x_249 = x_271;
x_250 = x_273;
x_251 = x_275;
x_252 = lean_box(0);
x_253 = x_281;
x_254 = x_279;
x_255 = x_270;
x_256 = x_272;
x_257 = x_276;
x_258 = x_278;
x_259 = x_277;
x_260 = x_280;
x_261 = x_283;
goto block_268;
}
}
block_301:
{
if (x_287 == 0)
{
if (x_37 == 0)
{
lean_dec_ref(x_295);
lean_dec(x_293);
lean_dec(x_289);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_195);
lean_dec_ref(x_31);
lean_dec(x_25);
lean_dec(x_24);
x_5 = lean_box(0);
x_6 = x_292;
goto block_9;
}
else
{
if (x_36 == 0)
{
if (x_296 == 0)
{
lean_dec_ref(x_295);
lean_dec(x_293);
lean_dec(x_289);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_195);
lean_dec_ref(x_31);
lean_dec(x_25);
lean_dec(x_24);
x_5 = lean_box(0);
x_6 = x_292;
goto block_9;
}
else
{
lean_object* x_297; uint32_t x_298; 
x_297 = l_Lake_JobAction_verb(x_288, x_294);
x_298 = 10004;
x_269 = x_285;
x_270 = x_286;
x_271 = x_287;
x_272 = x_289;
x_273 = x_288;
x_274 = lean_box(0);
x_275 = x_297;
x_276 = x_291;
x_277 = x_296;
x_278 = x_292;
x_279 = x_293;
x_280 = x_295;
x_281 = x_298;
goto block_284;
}
}
else
{
lean_dec_ref(x_295);
lean_dec(x_293);
lean_dec(x_289);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec_ref(x_195);
lean_dec_ref(x_31);
lean_dec(x_25);
lean_dec(x_24);
x_5 = lean_box(0);
x_6 = x_292;
goto block_9;
}
}
}
else
{
lean_object* x_299; uint32_t x_300; 
x_299 = l_Lake_JobAction_verb(x_288, x_294);
x_300 = l_Lake_LogLevel_icon(x_291);
x_269 = x_285;
x_270 = x_286;
x_271 = x_287;
x_272 = x_289;
x_273 = x_288;
x_274 = lean_box(0);
x_275 = x_299;
x_276 = x_291;
x_277 = x_287;
x_278 = x_292;
x_279 = x_293;
x_280 = x_295;
x_281 = x_300;
goto block_284;
}
}
block_314:
{
if (x_196 == 0)
{
x_285 = x_302;
x_286 = x_303;
x_287 = x_313;
x_288 = x_304;
x_289 = x_305;
x_290 = lean_box(0);
x_291 = x_307;
x_292 = x_308;
x_293 = x_309;
x_294 = x_311;
x_295 = x_312;
x_296 = x_310;
goto block_301;
}
else
{
if (x_35 == 0)
{
lean_dec_ref(x_312);
lean_dec(x_309);
lean_dec(x_305);
lean_dec(x_303);
lean_dec_ref(x_302);
lean_dec_ref(x_195);
lean_dec_ref(x_31);
lean_dec(x_25);
lean_dec(x_24);
x_5 = lean_box(0);
x_6 = x_308;
goto block_9;
}
else
{
x_285 = x_302;
x_286 = x_303;
x_287 = x_313;
x_288 = x_304;
x_289 = x_305;
x_290 = lean_box(0);
x_291 = x_307;
x_292 = x_308;
x_293 = x_309;
x_294 = x_311;
x_295 = x_312;
x_296 = x_310;
goto block_301;
}
}
}
block_340:
{
if (x_319 == 0)
{
if (x_318 == 0)
{
x_302 = x_315;
x_303 = x_316;
x_304 = x_319;
x_305 = x_317;
x_306 = lean_box(0);
x_307 = x_320;
x_308 = x_326;
x_309 = x_322;
x_310 = x_324;
x_311 = x_323;
x_312 = x_325;
x_313 = x_318;
goto block_314;
}
else
{
x_302 = x_315;
x_303 = x_316;
x_304 = x_319;
x_305 = x_317;
x_306 = lean_box(0);
x_307 = x_320;
x_308 = x_326;
x_309 = x_322;
x_310 = x_324;
x_311 = x_323;
x_312 = x_325;
x_313 = x_321;
goto block_314;
}
}
else
{
if (x_196 == 0)
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_326);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_326, 2);
lean_inc_ref(x_195);
x_330 = lean_array_push(x_329, x_195);
lean_ctor_set(x_326, 2, x_330);
x_302 = x_315;
x_303 = x_316;
x_304 = x_319;
x_305 = x_317;
x_306 = lean_box(0);
x_307 = x_320;
x_308 = x_326;
x_309 = x_322;
x_310 = x_324;
x_311 = x_323;
x_312 = x_325;
x_313 = x_319;
goto block_314;
}
else
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_331 = lean_ctor_get(x_326, 0);
x_332 = lean_ctor_get(x_326, 1);
x_333 = lean_ctor_get_uint8(x_326, sizeof(void*)*6);
x_334 = lean_ctor_get(x_326, 2);
x_335 = lean_ctor_get(x_326, 3);
x_336 = lean_ctor_get(x_326, 4);
x_337 = lean_ctor_get(x_326, 5);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_326);
lean_inc_ref(x_195);
x_338 = lean_array_push(x_334, x_195);
x_339 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_339, 0, x_331);
lean_ctor_set(x_339, 1, x_332);
lean_ctor_set(x_339, 2, x_338);
lean_ctor_set(x_339, 3, x_335);
lean_ctor_set(x_339, 4, x_336);
lean_ctor_set(x_339, 5, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*6, x_333);
x_302 = x_315;
x_303 = x_316;
x_304 = x_319;
x_305 = x_317;
x_306 = lean_box(0);
x_307 = x_320;
x_308 = x_339;
x_309 = x_322;
x_310 = x_324;
x_311 = x_323;
x_312 = x_325;
x_313 = x_319;
goto block_314;
}
}
else
{
x_302 = x_315;
x_303 = x_316;
x_304 = x_319;
x_305 = x_317;
x_306 = lean_box(0);
x_307 = x_320;
x_308 = x_326;
x_309 = x_322;
x_310 = x_324;
x_311 = x_323;
x_312 = x_325;
x_313 = x_319;
goto block_314;
}
}
}
block_361:
{
if (x_26 == 0)
{
uint8_t x_351; uint8_t x_352; 
x_351 = 3;
x_352 = l_Lake_instDecidableEqJobAction(x_349, x_351);
if (x_352 == 0)
{
x_315 = x_341;
x_316 = x_342;
x_317 = x_344;
x_318 = x_345;
x_319 = x_343;
x_320 = x_346;
x_321 = x_347;
x_322 = x_348;
x_323 = x_349;
x_324 = x_350;
x_325 = x_2;
x_326 = x_3;
x_327 = lean_box(0);
goto block_340;
}
else
{
uint8_t x_353; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc_ref(x_27);
x_353 = !lean_is_exclusive(x_3);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_354 = lean_ctor_get(x_3, 5);
lean_dec(x_354);
x_355 = lean_ctor_get(x_3, 4);
lean_dec(x_355);
x_356 = lean_ctor_get(x_3, 3);
lean_dec(x_356);
x_357 = lean_ctor_get(x_3, 2);
lean_dec(x_357);
x_358 = lean_ctor_get(x_3, 1);
lean_dec(x_358);
x_359 = lean_ctor_get(x_3, 0);
lean_dec(x_359);
lean_inc(x_25);
lean_inc(x_24);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_352);
x_315 = x_341;
x_316 = x_342;
x_317 = x_344;
x_318 = x_345;
x_319 = x_343;
x_320 = x_346;
x_321 = x_347;
x_322 = x_348;
x_323 = x_349;
x_324 = x_350;
x_325 = x_2;
x_326 = x_3;
x_327 = lean_box(0);
goto block_340;
}
else
{
lean_object* x_360; 
lean_dec(x_3);
lean_inc(x_25);
lean_inc(x_24);
x_360 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_360, 0, x_24);
lean_ctor_set(x_360, 1, x_25);
lean_ctor_set(x_360, 2, x_27);
lean_ctor_set(x_360, 3, x_28);
lean_ctor_set(x_360, 4, x_29);
lean_ctor_set(x_360, 5, x_30);
lean_ctor_set_uint8(x_360, sizeof(void*)*6, x_352);
x_315 = x_341;
x_316 = x_342;
x_317 = x_344;
x_318 = x_345;
x_319 = x_343;
x_320 = x_346;
x_321 = x_347;
x_322 = x_348;
x_323 = x_349;
x_324 = x_350;
x_325 = x_2;
x_326 = x_360;
x_327 = lean_box(0);
goto block_340;
}
}
}
else
{
x_315 = x_341;
x_316 = x_342;
x_317 = x_344;
x_318 = x_345;
x_319 = x_343;
x_320 = x_346;
x_321 = x_347;
x_322 = x_348;
x_323 = x_349;
x_324 = x_350;
x_325 = x_2;
x_326 = x_3;
x_327 = lean_box(0);
goto block_340;
}
}
block_374:
{
uint8_t x_371; 
x_371 = l_Lake_instOrdJobAction_ord(x_34, x_369);
if (x_371 == 2)
{
uint8_t x_372; 
x_372 = 0;
x_341 = x_362;
x_342 = x_363;
x_343 = x_366;
x_344 = x_365;
x_345 = x_364;
x_346 = x_367;
x_347 = x_370;
x_348 = x_368;
x_349 = x_369;
x_350 = x_372;
goto block_361;
}
else
{
uint8_t x_373; 
x_373 = 1;
x_341 = x_362;
x_342 = x_363;
x_343 = x_366;
x_344 = x_365;
x_345 = x_364;
x_346 = x_367;
x_347 = x_370;
x_348 = x_368;
x_349 = x_369;
x_350 = x_373;
goto block_361;
}
}
block_387:
{
uint8_t x_383; uint8_t x_384; 
x_383 = lean_strict_and(x_378, x_382);
x_384 = l_Lake_instOrdLogLevel_ord(x_32, x_379);
if (x_384 == 2)
{
uint8_t x_385; 
x_385 = 0;
x_362 = x_375;
x_363 = x_376;
x_364 = x_378;
x_365 = x_377;
x_366 = x_383;
x_367 = x_379;
x_368 = x_380;
x_369 = x_381;
x_370 = x_385;
goto block_374;
}
else
{
uint8_t x_386; 
x_386 = 1;
x_362 = x_375;
x_363 = x_376;
x_364 = x_378;
x_365 = x_377;
x_366 = x_383;
x_367 = x_379;
x_368 = x_380;
x_369 = x_381;
x_370 = x_386;
goto block_374;
}
}
block_400:
{
lean_object* x_389; uint8_t x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc_ref(x_389);
x_390 = lean_ctor_get_uint8(x_388, sizeof(void*)*3);
x_391 = lean_ctor_get(x_388, 2);
lean_inc(x_391);
lean_dec_ref(x_388);
x_392 = l_Lake_Log_maxLv(x_389);
x_393 = lean_array_get_size(x_389);
x_394 = lean_unsigned_to_nat(0u);
x_395 = lean_nat_dec_eq(x_393, x_394);
x_396 = l_instDecidableNot___redArg(x_395);
x_397 = l_Lake_instOrdLogLevel_ord(x_33, x_392);
if (x_397 == 2)
{
uint8_t x_398; 
x_398 = 0;
x_375 = x_389;
x_376 = x_393;
x_377 = x_391;
x_378 = x_396;
x_379 = x_392;
x_380 = x_394;
x_381 = x_390;
x_382 = x_398;
goto block_387;
}
else
{
uint8_t x_399; 
x_399 = 1;
x_375 = x_389;
x_376 = x_393;
x_377 = x_391;
x_378 = x_396;
x_379 = x_392;
x_380 = x_394;
x_381 = x_390;
x_382 = x_399;
goto block_387;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_1, x_10, x_11, x_4, x_12, x_13, x_7, x_8);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_array_uget(x_1, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_io_get_task_state(x_19);
lean_dec_ref(x_19);
switch (x_20) {
case 0:
{
uint8_t x_21; 
lean_inc(x_17);
lean_inc(x_16);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_push(x_17, x_18);
lean_ctor_set(x_4, 1, x_24);
x_8 = x_4;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_25 = lean_array_push(x_17, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_8 = x_26;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
case 1:
{
uint8_t x_27; 
lean_inc(x_17);
lean_inc(x_16);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_4, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_dec(x_29);
lean_inc_ref(x_18);
x_30 = lean_array_push(x_16, x_18);
x_31 = lean_array_push(x_17, x_18);
lean_ctor_set(x_4, 1, x_31);
lean_ctor_set(x_4, 0, x_30);
x_8 = x_4;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_inc_ref(x_18);
x_32 = lean_array_push(x_16, x_18);
x_33 = lean_array_push(x_17, x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_8 = x_34;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
default: 
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc_ref(x_5);
x_35 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(x_18, x_5, x_6);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_40);
x_8 = x_4;
x_9 = x_36;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
x_43 = lean_ctor_get_uint8(x_36, sizeof(void*)*6);
x_44 = lean_ctor_get(x_36, 2);
x_45 = lean_ctor_get(x_36, 3);
x_46 = lean_ctor_get(x_36, 4);
x_47 = lean_ctor_get(x_36, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_41, x_48);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*6, x_43);
x_8 = x_4;
x_9 = x_50;
x_10 = lean_box(0);
goto block_14;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec_ref(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_st_ref_take(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lake_mkBuildContext___closed__0;
x_9 = lean_st_ref_set(x_5, x_8);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_array_get_size(x_6);
x_23 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_23);
x_24 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_25 = lean_array_get_size(x_1);
x_26 = lean_nat_dec_lt(x_7, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_inc_ref(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_3);
x_13 = x_27;
x_14 = x_24;
x_15 = x_3;
x_16 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_25, x_25);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_25);
lean_inc_ref(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_3);
x_13 = x_29;
x_14 = x_24;
x_15 = x_3;
x_16 = lean_box(0);
goto block_22;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_25);
lean_dec(x_25);
lean_inc_ref(x_2);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_30, x_31, x_24, x_2, x_3);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_13 = x_32;
x_14 = x_33;
x_15 = x_34;
x_16 = lean_box(0);
goto block_22;
}
}
block_22:
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_7, x_12);
if (x_17 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_12, x_12);
if (x_18 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec_ref(x_13);
x_19 = 0;
x_20 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_19, x_20, x_14, x_2, x_15);
lean_dec_ref(x_6);
return x_21;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_38 = lean_ctor_get(x_3, 2);
x_39 = lean_ctor_get(x_3, 3);
x_40 = lean_ctor_get(x_3, 4);
x_41 = lean_ctor_get(x_3, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_42 = lean_array_get_size(x_6);
x_53 = lean_nat_add(x_36, x_42);
lean_dec(x_36);
x_54 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_38);
lean_ctor_set(x_54, 3, x_39);
lean_ctor_set(x_54, 4, x_40);
lean_ctor_set(x_54, 5, x_41);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_37);
x_55 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_56 = lean_array_get_size(x_1);
x_57 = lean_nat_dec_lt(x_7, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
lean_inc_ref(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_54);
x_43 = x_58;
x_44 = x_55;
x_45 = x_54;
x_46 = lean_box(0);
goto block_52;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_56, x_56);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_56);
lean_inc_ref(x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_54);
x_43 = x_60;
x_44 = x_55;
x_45 = x_54;
x_46 = lean_box(0);
goto block_52;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_56);
lean_dec(x_56);
lean_inc_ref(x_2);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_61, x_62, x_55, x_2, x_54);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
x_43 = x_63;
x_44 = x_64;
x_45 = x_65;
x_46 = lean_box(0);
goto block_52;
}
}
block_52:
{
uint8_t x_47; 
x_47 = lean_nat_dec_lt(x_7, x_42);
if (x_47 == 0)
{
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_42);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_43;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_42, x_42);
if (x_48 == 0)
{
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_42);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_43;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
lean_dec_ref(x_43);
x_49 = 0;
x_50 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_49, x_50, x_44, x_2, x_45);
lean_dec_ref(x_6);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_io_mono_ms_now();
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
x_4 = x_2;
x_5 = lean_box(0);
goto block_20;
}
else
{
uint32_t x_28; lean_object* x_29; 
x_28 = lean_uint32_of_nat(x_25);
lean_dec(x_25);
x_29 = l_IO_sleep(x_28);
x_4 = x_2;
x_5 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_mono_ms_now();
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 4);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 4, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_6);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*6, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_6, 1, x_7);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
lean_inc_ref(x_2);
x_15 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_9, x_10, x_2, x_7);
lean_dec(x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_1 = x_10;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_2);
x_27 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_20, x_21, x_2, x_7);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_1 = x_21;
x_3 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_loop(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_loop(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
lean_ctor_set(x_6, 3, x_10);
x_15 = lean_string_utf8_byte_size(x_9);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 4);
lean_inc_ref(x_20);
lean_dec_ref(x_18);
lean_inc_ref(x_9);
x_26 = lean_apply_2(x_20, x_9, lean_box(0));
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_9);
x_21 = lean_box(0);
goto block_25;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_30 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_31 = lean_unsigned_to_nat(84u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_34 = lean_io_error_to_string(x_28);
x_35 = lean_string_append(x_33, x_34);
lean_dec_ref(x_34);
x_36 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_String_quote(x_9);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 0, x_38);
x_39 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_40 = l_Std_Format_pretty(x_26, x_39, x_16, x_16);
x_41 = lean_string_append(x_37, x_40);
lean_dec_ref(x_40);
x_42 = l_mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_41);
lean_dec_ref(x_41);
x_43 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_42);
x_21 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_ctor_get(x_26, 0);
lean_inc(x_44);
lean_dec(x_26);
x_45 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_46 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_47 = lean_unsigned_to_nat(84u);
x_48 = lean_unsigned_to_nat(4u);
x_49 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_50 = lean_io_error_to_string(x_44);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_String_quote(x_9);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_57 = l_Std_Format_pretty(x_55, x_56, x_16, x_16);
x_58 = lean_string_append(x_53, x_57);
lean_dec_ref(x_57);
x_59 = l_mkPanicMessageWithDecl(x_45, x_46, x_47, x_48, x_58);
lean_dec_ref(x_58);
x_60 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_59);
x_21 = lean_box(0);
goto block_25;
}
}
block_25:
{
lean_object* x_22; 
x_22 = lean_apply_1(x_19, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_11 = x_23;
x_12 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_22);
x_24 = lean_box(0);
x_11 = x_24;
x_12 = lean_box(0);
goto block_14;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_6);
return x_62;
}
block_14:
{
lean_object* x_13; 
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_63 = lean_ctor_get(x_6, 0);
x_64 = lean_ctor_get(x_6, 1);
x_65 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_66 = lean_ctor_get(x_6, 2);
x_67 = lean_ctor_get(x_6, 3);
x_68 = lean_ctor_get(x_6, 4);
x_69 = lean_ctor_get(x_6, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_6);
x_70 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_71 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*6, x_65);
x_76 = lean_string_utf8_byte_size(x_67);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_87; 
x_79 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_2);
x_80 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_81);
lean_dec_ref(x_79);
lean_inc_ref(x_67);
x_87 = lean_apply_2(x_81, x_67, lean_box(0));
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
lean_dec_ref(x_67);
x_82 = lean_box(0);
goto block_86;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_91 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_92 = lean_unsigned_to_nat(84u);
x_93 = lean_unsigned_to_nat(4u);
x_94 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_95 = lean_io_error_to_string(x_88);
x_96 = lean_string_append(x_94, x_95);
lean_dec_ref(x_95);
x_97 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_98 = lean_string_append(x_96, x_97);
x_99 = l_String_quote(x_67);
if (lean_is_scalar(x_89)) {
 x_100 = lean_alloc_ctor(3, 1, 0);
} else {
 x_100 = x_89;
 lean_ctor_set_tag(x_100, 3);
}
lean_ctor_set(x_100, 0, x_99);
x_101 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_102 = l_Std_Format_pretty(x_100, x_101, x_77, x_77);
x_103 = lean_string_append(x_98, x_102);
lean_dec_ref(x_102);
x_104 = l_mkPanicMessageWithDecl(x_90, x_91, x_92, x_93, x_103);
lean_dec_ref(x_103);
x_105 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_104);
x_82 = lean_box(0);
goto block_86;
}
block_86:
{
lean_object* x_83; 
x_83 = lean_apply_1(x_80, lean_box(0));
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_72 = x_84;
x_73 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_85; 
lean_dec_ref(x_83);
x_85 = lean_box(0);
x_72 = x_85;
x_73 = lean_box(0);
goto block_75;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_67);
lean_dec(x_7);
lean_dec_ref(x_2);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_71);
return x_107;
}
block_75:
{
lean_object* x_74; 
if (lean_is_scalar(x_7)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_7;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_main(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorResult_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MonitorResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_io_mono_ms_now();
x_16 = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 4, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 5, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*3 + 6, x_10);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_11);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_18);
x_20 = l___private_Lake_Build_Run_0__Lake_Monitor_main(x_1, x_16, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*6);
x_24 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = lean_unbox(x_8);
x_20 = lean_unbox(x_9);
x_21 = lean_unbox(x_10);
x_22 = l_Lake_monitorJobs(x_1, x_2, x_3, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_11, x_12, x_13);
return x_22;
}
}
static uint32_t _init_l_Lake_noBuildCode() {
_start:
{
uint32_t x_1; 
x_1 = 3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_get_set_stdout(x_1);
lean_dec_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_get_set_stdout(x_1);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_15, x_17, x_20, x_19);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_box(0);
x_29 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_15, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_10 = x_26;
x_11 = x_30;
x_12 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_get_set_stdin(x_1);
lean_dec_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_get_set_stdin(x_1);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_15, x_17, x_20, x_19);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_box(0);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_15, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_10 = x_26;
x_11 = x_30;
x_12 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_get_set_stderr(x_1);
lean_dec_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_get_set_stderr(x_1);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(x_15, x_17, x_20, x_19);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_box(0);
x_29 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(x_15, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_10 = x_26;
x_11 = x_30;
x_12 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_1 = lean_mk_string_unchecked("Init.Data.String.Basic", 22, 22);
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
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(244u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
x_18 = lean_st_mk_ref(x_17);
x_19 = lean_st_mk_ref(x_17);
x_20 = l_IO_FS_Stream_ofBuffer(x_18);
lean_inc(x_19);
x_21 = l_IO_FS_Stream_ofBuffer(x_19);
if (x_2 == 0)
{
x_22 = x_1;
goto block_37;
}
else
{
lean_object* x_38; 
lean_inc_ref(x_21);
x_38 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___boxed), 10, 3);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, x_21);
lean_closure_set(x_38, 2, x_1);
x_22 = x_38;
goto block_37;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
block_37:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___boxed), 10, 3);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_22);
x_24 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_20, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_st_ref_get(x_19);
lean_dec(x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
lean_inc_ref(x_28);
x_29 = lean_string_validate_utf8(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_28);
x_30 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
x_31 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(x_30);
x_10 = x_25;
x_11 = x_26;
x_12 = lean_box(0);
x_13 = x_31;
goto block_16;
}
else
{
lean_object* x_32; 
x_32 = lean_string_from_utf8_unchecked(x_28);
x_10 = x_25;
x_11 = x_26;
x_12 = lean_box(0);
x_13 = x_32;
goto block_16;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("- ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_array_uget(x_2, x_3);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0;
x_17 = lean_string_append(x_16, x_15);
lean_dec_ref(x_15);
x_18 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
x_19 = lean_string_append(x_17, x_18);
lean_inc_ref(x_14);
lean_inc_ref(x_19);
x_20 = lean_apply_2(x_14, x_19, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_7 = x_21;
x_8 = lean_box(0);
goto block_12;
}
else
{
lean_dec_ref(x_1);
return x_20;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_25 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_26 = lean_unsigned_to_nat(84u);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_30 = lean_io_error_to_string(x_23);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_String_quote(x_19);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 0, x_34);
x_35 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_36 = l_Std_Format_pretty(x_20, x_35, x_28, x_28);
x_37 = lean_string_append(x_33, x_36);
lean_dec_ref(x_36);
x_38 = l_mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_37);
lean_dec_ref(x_37);
x_39 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_38);
x_7 = x_39;
x_8 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_42 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_43 = lean_unsigned_to_nat(84u);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_47 = lean_io_error_to_string(x_40);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_String_quote(x_19);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_54 = l_Std_Format_pretty(x_52, x_53, x_45, x_45);
x_55 = lean_string_append(x_50, x_54);
lean_dec_ref(x_54);
x_56 = l_mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_55);
lean_dec_ref(x_55);
x_57 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_56);
x_7 = x_57;
x_8 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_1);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_5);
return x_58;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_array_uget(x_2, x_3);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0;
x_17 = lean_string_append(x_16, x_15);
lean_dec_ref(x_15);
x_18 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
x_19 = lean_string_append(x_17, x_18);
lean_inc_ref(x_14);
lean_inc_ref(x_19);
x_20 = lean_apply_2(x_14, x_19, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_7 = x_21;
x_8 = lean_box(0);
goto block_12;
}
else
{
lean_dec_ref(x_1);
return x_20;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_25 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_26 = lean_unsigned_to_nat(84u);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_30 = lean_io_error_to_string(x_23);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_String_quote(x_19);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 0, x_34);
x_35 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_36 = l_Std_Format_pretty(x_20, x_35, x_28, x_28);
x_37 = lean_string_append(x_33, x_36);
lean_dec_ref(x_36);
x_38 = l_mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_37);
lean_dec_ref(x_37);
x_39 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_38);
x_7 = x_39;
x_8 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_42 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_43 = lean_unsigned_to_nat(84u);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_47 = lean_io_error_to_string(x_40);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_String_quote(x_19);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_54 = l_Std_Format_pretty(x_52, x_53, x_45, x_45);
x_55 = lean_string_append(x_50, x_54);
lean_dec_ref(x_54);
x_56 = l_mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_55);
lean_dec_ref(x_55);
x_57 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_56);
x_7 = x_57;
x_8 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_1);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_5);
return x_58;
}
block_12:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(x_1, x_2, x_10, x_4, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9_spec__9(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_2, x_3);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_2, x_3);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9_spec__9(x_1, x_2, x_3, x_4, x_13, x_6, x_11);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_10, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_7, 0, x_13);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_11, 1, x_7);
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
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_7);
x_26 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_22, lean_box(0));
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_23);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_23);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_21 = lean_string_utf8_byte_size(x_15);
x_22 = lean_nat_dec_eq(x_21, x_9);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0;
x_26 = l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(x_15, x_21, x_9);
x_27 = l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(x_15, x_26, x_21);
x_28 = lean_string_utf8_extract(x_15, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_15);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_24, x_31);
lean_ctor_set(x_13, 0, x_32);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_13, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_37 = l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0;
x_38 = l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(x_15, x_21, x_9);
x_39 = l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(x_15, x_38, x_21);
x_40 = lean_string_utf8_extract(x_15, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_15);
x_41 = lean_string_append(x_37, x_40);
lean_dec_ref(x_40);
x_42 = 1;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_push(x_33, x_43);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_34);
x_17 = x_45;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_19; 
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
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
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0;
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 3;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Some required targets logged failures:\n", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Build completed successfully (", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(").\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("All targets up-to-date (", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" jobs", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1 job", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Uncaught top-level build failure (this is likely a bug in Lake).\n", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_18; lean_object* x_22; uint8_t x_26; 
x_26 = l_Array_isEmpty___redArg(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_44; lean_object* x_45; 
lean_dec(x_8);
lean_dec_ref(x_7);
x_27 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_2, 4);
x_44 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3;
lean_inc_ref(x_28);
x_45 = lean_apply_2(x_28, x_44, lean_box(0));
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_32 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_48 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_49 = lean_unsigned_to_nat(84u);
x_50 = lean_unsigned_to_nat(4u);
x_51 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_52 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_53 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_5);
x_54 = l_Lean_Name_num___override(x_53, x_5);
x_55 = l_Lean_Name_str___override(x_54, x_52);
x_56 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_57 = l_Lean_Name_str___override(x_55, x_56);
x_58 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_57, x_6);
x_59 = lean_string_append(x_51, x_58);
lean_dec_ref(x_58);
x_60 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_io_error_to_string(x_46);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__5;
x_67 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc_n(x_5, 2);
x_68 = l_Std_Format_pretty(x_66, x_67, x_5, x_5);
x_69 = lean_string_append(x_65, x_68);
lean_dec_ref(x_68);
x_70 = l_mkPanicMessageWithDecl(x_47, x_48, x_49, x_50, x_69);
lean_dec_ref(x_69);
x_71 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_70);
x_32 = lean_box(0);
goto block_43;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_apply_1(x_27, lean_box(0));
lean_dec_ref(x_30);
x_18 = lean_box(0);
goto block_21;
}
block_43:
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_1);
x_34 = lean_nat_dec_lt(x_5, x_33);
lean_dec(x_5);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec_ref(x_2);
x_29 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_33, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec_ref(x_2);
x_29 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_36 = lean_box(0);
x_37 = 0;
x_38 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(x_2, x_1, x_37, x_38, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
x_29 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_40; 
lean_dec_ref(x_27);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
}
else
{
lean_object* x_72; 
x_72 = lean_io_wait(x_7);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
if (x_10 == 0)
{
lean_object* x_207; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_73);
return x_207;
}
else
{
if (x_11 == 0)
{
lean_object* x_208; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_73);
return x_208;
}
else
{
uint8_t x_209; 
x_209 = lean_nat_dec_eq(x_8, x_9);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = l_Nat_reprFast(x_8);
x_211 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__9;
x_212 = lean_string_append(x_210, x_211);
x_74 = x_11;
x_75 = x_212;
goto block_206;
}
else
{
lean_object* x_213; 
lean_dec(x_8);
x_213 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__10;
x_74 = x_11;
x_75 = x_213;
goto block_206;
}
}
}
block_206:
{
if (x_3 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_76);
lean_dec_ref(x_2);
x_77 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__6;
x_78 = lean_string_append(x_77, x_75);
lean_dec_ref(x_75);
x_79 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7;
x_80 = lean_string_append(x_78, x_79);
lean_inc_ref(x_80);
x_81 = lean_apply_2(x_76, x_80, lean_box(0));
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec_ref(x_80);
lean_dec(x_5);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_73);
return x_81;
}
else
{
lean_object* x_84; 
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_73);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_88 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_89 = lean_unsigned_to_nat(84u);
x_90 = lean_unsigned_to_nat(4u);
x_91 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_92 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_93 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_5);
x_94 = l_Lean_Name_num___override(x_93, x_5);
x_95 = l_Lean_Name_str___override(x_94, x_92);
x_96 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_97 = l_Lean_Name_str___override(x_95, x_96);
x_98 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_97, x_74);
x_99 = lean_string_append(x_91, x_98);
lean_dec_ref(x_98);
x_100 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_io_error_to_string(x_86);
x_103 = lean_string_append(x_101, x_102);
lean_dec_ref(x_102);
x_104 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_105 = lean_string_append(x_103, x_104);
x_106 = l_String_quote(x_80);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc(x_5);
x_109 = l_Std_Format_pretty(x_107, x_108, x_5, x_5);
x_110 = lean_string_append(x_105, x_109);
lean_dec_ref(x_109);
x_111 = l_mkPanicMessageWithDecl(x_87, x_88, x_89, x_90, x_110);
lean_dec_ref(x_110);
x_112 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_111);
lean_ctor_set_tag(x_81, 0);
lean_ctor_set(x_81, 0, x_73);
return x_81;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_113 = lean_ctor_get(x_81, 0);
lean_inc(x_113);
lean_dec(x_81);
x_114 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_115 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_116 = lean_unsigned_to_nat(84u);
x_117 = lean_unsigned_to_nat(4u);
x_118 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_119 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_120 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_5);
x_121 = l_Lean_Name_num___override(x_120, x_5);
x_122 = l_Lean_Name_str___override(x_121, x_119);
x_123 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_124 = l_Lean_Name_str___override(x_122, x_123);
x_125 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_124, x_74);
x_126 = lean_string_append(x_118, x_125);
lean_dec_ref(x_125);
x_127 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_io_error_to_string(x_113);
x_130 = lean_string_append(x_128, x_129);
lean_dec_ref(x_129);
x_131 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_132 = lean_string_append(x_130, x_131);
x_133 = l_String_quote(x_80);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc(x_5);
x_136 = l_Std_Format_pretty(x_134, x_135, x_5, x_5);
x_137 = lean_string_append(x_132, x_136);
lean_dec_ref(x_136);
x_138 = l_mkPanicMessageWithDecl(x_114, x_115, x_116, x_117, x_137);
lean_dec_ref(x_137);
x_139 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_138);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_73);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_141);
lean_dec_ref(x_2);
x_142 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__8;
x_143 = lean_string_append(x_142, x_75);
lean_dec_ref(x_75);
x_144 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7;
x_145 = lean_string_append(x_143, x_144);
lean_inc_ref(x_145);
x_146 = lean_apply_2(x_141, x_145, lean_box(0));
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
lean_dec_ref(x_145);
lean_dec(x_5);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_146, 0);
lean_dec(x_148);
lean_ctor_set(x_146, 0, x_73);
return x_146;
}
else
{
lean_object* x_149; 
lean_dec(x_146);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_73);
return x_149;
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_146);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_151 = lean_ctor_get(x_146, 0);
x_152 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_153 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_154 = lean_unsigned_to_nat(84u);
x_155 = lean_unsigned_to_nat(4u);
x_156 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_157 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_158 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_5);
x_159 = l_Lean_Name_num___override(x_158, x_5);
x_160 = l_Lean_Name_str___override(x_159, x_157);
x_161 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_162 = l_Lean_Name_str___override(x_160, x_161);
x_163 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_162, x_3);
x_164 = lean_string_append(x_156, x_163);
lean_dec_ref(x_163);
x_165 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_166 = lean_string_append(x_164, x_165);
x_167 = lean_io_error_to_string(x_151);
x_168 = lean_string_append(x_166, x_167);
lean_dec_ref(x_167);
x_169 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_170 = lean_string_append(x_168, x_169);
x_171 = l_String_quote(x_145);
x_172 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc(x_5);
x_174 = l_Std_Format_pretty(x_172, x_173, x_5, x_5);
x_175 = lean_string_append(x_170, x_174);
lean_dec_ref(x_174);
x_176 = l_mkPanicMessageWithDecl(x_152, x_153, x_154, x_155, x_175);
lean_dec_ref(x_175);
x_177 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_176);
lean_ctor_set_tag(x_146, 0);
lean_ctor_set(x_146, 0, x_73);
return x_146;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_178 = lean_ctor_get(x_146, 0);
lean_inc(x_178);
lean_dec(x_146);
x_179 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_180 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_181 = lean_unsigned_to_nat(84u);
x_182 = lean_unsigned_to_nat(4u);
x_183 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_184 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_185 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_5);
x_186 = l_Lean_Name_num___override(x_185, x_5);
x_187 = l_Lean_Name_str___override(x_186, x_184);
x_188 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_189 = l_Lean_Name_str___override(x_187, x_188);
x_190 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_189, x_3);
x_191 = lean_string_append(x_183, x_190);
lean_dec_ref(x_190);
x_192 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_193 = lean_string_append(x_191, x_192);
x_194 = lean_io_error_to_string(x_178);
x_195 = lean_string_append(x_193, x_194);
lean_dec_ref(x_194);
x_196 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_197 = lean_string_append(x_195, x_196);
x_198 = l_String_quote(x_145);
x_199 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc(x_5);
x_201 = l_Std_Format_pretty(x_199, x_200, x_5, x_5);
x_202 = lean_string_append(x_197, x_201);
lean_dec_ref(x_201);
x_203 = l_mkPanicMessageWithDecl(x_179, x_180, x_181, x_182, x_202);
lean_dec_ref(x_202);
x_204 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_203);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_73);
return x_205;
}
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec_ref(x_72);
lean_dec(x_8);
x_214 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_214);
lean_dec_ref(x_2);
x_215 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11;
x_216 = lean_apply_2(x_214, x_215, lean_box(0));
if (lean_obj_tag(x_216) == 0)
{
lean_dec_ref(x_216);
lean_dec(x_5);
x_22 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_219 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_220 = lean_unsigned_to_nat(84u);
x_221 = lean_unsigned_to_nat(4u);
x_222 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_223 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_224 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_5);
x_225 = l_Lean_Name_num___override(x_224, x_5);
x_226 = l_Lean_Name_str___override(x_225, x_223);
x_227 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_228 = l_Lean_Name_str___override(x_226, x_227);
x_229 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_228, x_26);
x_230 = lean_string_append(x_222, x_229);
lean_dec_ref(x_229);
x_231 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_232 = lean_string_append(x_230, x_231);
x_233 = lean_io_error_to_string(x_217);
x_234 = lean_string_append(x_232, x_233);
lean_dec_ref(x_233);
x_235 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_236 = lean_string_append(x_234, x_235);
x_237 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__13;
x_238 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc(x_5);
x_239 = l_Std_Format_pretty(x_237, x_238, x_5, x_5);
x_240 = lean_string_append(x_236, x_239);
lean_dec_ref(x_239);
x_241 = l_mkPanicMessageWithDecl(x_218, x_219, x_220, x_221, x_240);
lean_dec_ref(x_240);
x_242 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_241);
x_22 = lean_box(0);
goto block_25;
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_21:
{
if (x_3 == 0)
{
x_14 = lean_box(0);
goto block_17;
}
else
{
if (x_4 == 0)
{
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__2;
x_20 = lean_io_exit(x_19);
return x_20;
}
}
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__2;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_Workspace_runFetchM___redArg___closed__3;
x_3 = 0;
x_4 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("job computation", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n", 87, 87);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__6;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__8;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("There were issues saving input-to-output mappings from the build:\n", 66, 66);
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
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__12;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to save input-to-output mappings from the build.\n", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__14;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__16;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache.", 161, 161);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_148; uint8_t x_149; uint8_t x_180; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_16 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 1);
x_17 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 2);
x_18 = lean_ctor_get(x_10, 0);
x_19 = l_Lake_OutStream_get(x_18);
lean_inc_ref(x_19);
x_20 = l_Lake_AnsiMode_isEnabled(x_19, x_17);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_21 = l_Lake_mkBuildContext(x_1, x_3);
x_22 = lean_box(1);
x_23 = lean_st_mk_ref(x_22);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_24, 0, x_2);
x_25 = lean_unsigned_to_nat(0u);
x_41 = lean_box(0);
x_42 = lean_box(0);
x_43 = l_Lake_Workspace_runFetchM___redArg___closed__0;
x_44 = 1;
x_45 = l_Lake_Workspace_runFetchM___redArg___closed__1;
x_46 = 0;
x_47 = l_Lake_Workspace_runFetchM___redArg___closed__4;
x_48 = lean_box(x_44);
lean_inc_ref(x_21);
lean_inc(x_23);
x_49 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_49, 0, x_24);
lean_closure_set(x_49, 1, x_48);
lean_closure_set(x_49, 2, x_43);
lean_closure_set(x_49, 3, x_42);
lean_closure_set(x_49, 4, x_41);
lean_closure_set(x_49, 5, x_23);
lean_closure_set(x_49, 6, x_21);
lean_closure_set(x_49, 7, x_47);
lean_closure_set(x_49, 8, x_25);
x_50 = lean_io_as_task(x_49, x_25);
x_51 = lean_st_ref_get(x_23);
lean_dec(x_23);
lean_dec(x_51);
x_52 = lean_box(0);
x_53 = l_Lake_BuildConfig_showProgress(x_3);
lean_dec_ref(x_3);
x_54 = l_Lake_Workspace_runFetchM___redArg___closed__5;
x_55 = 0;
lean_inc_ref(x_50);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_55);
x_57 = 2;
x_58 = l_Lake_instDecidableEqVerbosity(x_12, x_57);
if (x_58 == 0)
{
uint8_t x_182; 
x_182 = 2;
x_180 = x_182;
goto block_181;
}
else
{
x_180 = x_46;
goto block_181;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, x_7, lean_box(0));
return x_8;
}
block_40:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_array_get_size(x_26);
x_30 = lean_box(0);
x_31 = lean_nat_dec_lt(x_25, x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
x_32 = lean_apply_2(x_27, x_30, lean_box(0));
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_29, x_29);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
x_34 = lean_apply_2(x_27, x_30, lean_box(0));
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(x_19, x_16, x_20, x_26, x_35, x_36, x_30);
lean_dec_ref(x_26);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_apply_2(x_27, x_38, lean_box(0));
return x_39;
}
}
}
block_75:
{
if (x_58 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_59);
lean_dec_ref(x_19);
x_62 = lean_box(0);
x_63 = lean_apply_2(x_60, x_62, lean_box(0));
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_array_get_size(x_59);
x_65 = lean_box(0);
x_66 = lean_nat_dec_lt(x_25, x_64);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_19);
x_67 = lean_apply_2(x_60, x_65, lean_box(0));
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_64, x_64);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_64);
lean_dec_ref(x_59);
lean_dec_ref(x_19);
x_69 = lean_apply_2(x_60, x_65, lean_box(0));
return x_69;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(x_19, x_16, x_20, x_59, x_70, x_71, x_65);
lean_dec_ref(x_59);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_apply_2(x_60, x_73, lean_box(0));
return x_74;
}
}
}
}
block_147:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_79);
lean_dec_ref(x_1);
x_80 = lean_ctor_get(x_79, 21);
lean_inc(x_80);
lean_dec_ref(x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_76);
x_81 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_81);
lean_dec_ref(x_19);
x_82 = l_Lake_Workspace_runFetchM___redArg___closed__6;
x_83 = lean_apply_2(x_81, x_82, lean_box(0));
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_apply_2(x_77, x_84, lean_box(0));
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec_ref(x_83);
x_87 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_88 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_89 = lean_unsigned_to_nat(84u);
x_90 = lean_unsigned_to_nat(4u);
x_91 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_92 = lean_io_error_to_string(x_86);
x_93 = lean_string_append(x_91, x_92);
lean_dec_ref(x_92);
x_94 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_95 = lean_string_append(x_93, x_94);
x_96 = l_Lake_Workspace_runFetchM___redArg___closed__9;
x_97 = lean_string_append(x_95, x_96);
x_98 = l_mkPanicMessageWithDecl(x_87, x_88, x_89, x_90, x_97);
lean_dec_ref(x_97);
x_99 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_98);
x_100 = lean_apply_2(x_77, x_99, lean_box(0));
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
lean_dec_ref(x_80);
x_102 = lean_st_ref_get(x_101);
lean_dec(x_101);
x_103 = l_Lake_CacheMap_writeFile(x_76, x_102, x_45);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_array_get_size(x_104);
x_106 = lean_nat_dec_eq(x_105, x_25);
lean_dec(x_105);
if (x_106 == 0)
{
if (x_58 == 0)
{
lean_dec(x_104);
lean_dec_ref(x_19);
x_5 = lean_box(0);
x_6 = x_77;
goto block_9;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_107);
x_108 = l_Lake_Workspace_runFetchM___redArg___closed__10;
x_109 = lean_apply_2(x_107, x_108, lean_box(0));
if (lean_obj_tag(x_109) == 0)
{
lean_dec_ref(x_109);
x_26 = x_104;
x_27 = x_77;
x_28 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_112 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_113 = lean_unsigned_to_nat(84u);
x_114 = lean_unsigned_to_nat(4u);
x_115 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_116 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_117 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_116, x_58);
x_118 = lean_string_append(x_115, x_117);
lean_dec_ref(x_117);
x_119 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_io_error_to_string(x_110);
x_122 = lean_string_append(x_120, x_121);
lean_dec_ref(x_121);
x_123 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_124 = lean_string_append(x_122, x_123);
x_125 = l_Lake_Workspace_runFetchM___redArg___closed__13;
x_126 = lean_string_append(x_124, x_125);
x_127 = l_mkPanicMessageWithDecl(x_111, x_112, x_113, x_114, x_126);
lean_dec_ref(x_126);
x_128 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_127);
x_26 = x_104;
x_27 = x_77;
x_28 = lean_box(0);
goto block_40;
}
}
}
else
{
lean_dec(x_104);
lean_dec_ref(x_19);
x_5 = lean_box(0);
x_6 = x_77;
goto block_9;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_103, 1);
lean_inc(x_129);
lean_dec_ref(x_103);
x_130 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_130);
x_131 = l_Lake_Workspace_runFetchM___redArg___closed__14;
x_132 = lean_apply_2(x_130, x_131, lean_box(0));
if (lean_obj_tag(x_132) == 0)
{
lean_dec_ref(x_132);
x_59 = x_129;
x_60 = x_77;
x_61 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_135 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_136 = lean_unsigned_to_nat(84u);
x_137 = lean_unsigned_to_nat(4u);
x_138 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_139 = lean_io_error_to_string(x_133);
x_140 = lean_string_append(x_138, x_139);
lean_dec_ref(x_139);
x_141 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_142 = lean_string_append(x_140, x_141);
x_143 = l_Lake_Workspace_runFetchM___redArg___closed__17;
x_144 = lean_string_append(x_142, x_143);
x_145 = l_mkPanicMessageWithDecl(x_134, x_135, x_136, x_137, x_144);
lean_dec_ref(x_144);
x_146 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_145);
x_59 = x_129;
x_60 = x_77;
x_61 = lean_box(0);
goto block_75;
}
}
}
}
block_179:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_150 = lean_ctor_get(x_21, 3);
lean_inc(x_150);
lean_dec_ref(x_21);
x_151 = l_Lake_Job_toOpaque___redArg(x_56);
x_152 = lean_unsigned_to_nat(1u);
x_153 = l_Lake_Workspace_runFetchM___redArg___closed__18;
x_154 = lean_array_push(x_153, x_151);
x_155 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_156 = lean_unsigned_to_nat(100u);
lean_inc_ref(x_19);
x_157 = l_Lake_monitorJobs(x_154, x_150, x_19, x_15, x_16, x_148, x_58, x_20, x_53, x_149, x_155, x_45, x_156);
x_158 = lean_ctor_get_uint8(x_157, sizeof(void*)*2);
x_159 = lean_ctor_get(x_157, 0);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec_ref(x_157);
x_161 = lean_box(x_11);
x_162 = lean_box(x_158);
x_163 = lean_box(x_44);
x_164 = lean_box(x_53);
x_165 = lean_box(x_13);
lean_inc(x_160);
lean_inc_ref(x_50);
lean_inc_ref(x_19);
lean_inc_ref(x_159);
x_166 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__2___boxed), 13, 11);
lean_closure_set(x_166, 0, x_159);
lean_closure_set(x_166, 1, x_19);
lean_closure_set(x_166, 2, x_161);
lean_closure_set(x_166, 3, x_162);
lean_closure_set(x_166, 4, x_25);
lean_closure_set(x_166, 5, x_163);
lean_closure_set(x_166, 6, x_50);
lean_closure_set(x_166, 7, x_160);
lean_closure_set(x_166, 8, x_152);
lean_closure_set(x_166, 9, x_164);
lean_closure_set(x_166, 10, x_165);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_166);
lean_dec_ref(x_1);
x_167 = lean_box(0);
x_168 = l_Lake_Workspace_runFetchM___redArg___lam__2(x_159, x_19, x_11, x_158, x_25, x_44, x_50, x_160, x_152, x_53, x_13, x_167);
lean_dec_ref(x_159);
return x_168;
}
else
{
lean_object* x_169; uint8_t x_170; 
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec_ref(x_50);
x_169 = lean_ctor_get(x_14, 0);
lean_inc(x_169);
lean_dec_ref(x_14);
x_170 = l_Lake_Workspace_isRootArtifactCacheEnabled(x_1);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_1, 0);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_172, x_44);
x_174 = l_Lake_Workspace_runFetchM___redArg___closed__19;
x_175 = lean_string_append(x_173, x_174);
x_176 = 2;
x_177 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_176);
lean_inc_ref(x_19);
x_178 = l_Lake_logToStream(x_177, x_19, x_16, x_20);
lean_dec_ref(x_177);
x_76 = x_169;
x_77 = x_166;
x_78 = lean_box(0);
goto block_147;
}
else
{
x_76 = x_169;
x_77 = x_166;
x_78 = lean_box(0);
goto block_147;
}
}
}
block_181:
{
if (x_58 == 0)
{
if (x_20 == 0)
{
x_148 = x_180;
x_149 = x_44;
goto block_179;
}
else
{
x_148 = x_180;
x_149 = x_58;
goto block_179;
}
}
else
{
x_148 = x_180;
x_149 = x_58;
goto block_179;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9_spec__9(x_1, x_9, x_10, x_4, x_11, x_12, x_7);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(x_1, x_9, x_10, x_4, x_11, x_12, x_7);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Workspace_runFetchM___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_Workspace_runFetchM___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_6);
x_17 = lean_unbox(x_10);
x_18 = lean_unbox(x_11);
x_19 = l_Lake_Workspace_runFetchM___redArg___lam__2(x_1, x_2, x_14, x_15, x_5, x_16, x_7, x_8, x_9, x_17, x_18, x_12);
lean_dec(x_9);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_io_wait(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_9);
x_11 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_io_wait(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_14);
x_17 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_io_wait(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_10);
x_12 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_io_wait(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_15);
x_18 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runBuild___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runBuild(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_3, x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_io_wait(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_9);
x_11 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_io_wait(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_14);
x_17 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_4, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_io_wait(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_10);
x_12 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_io_wait(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_15);
x_18 = l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1;
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_runBuild___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_runBuild(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Index(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Run(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkBuildContext___closed__0 = _init_l_Lake_mkBuildContext___closed__0();
lean_mark_persistent(l_Lake_mkBuildContext___closed__0);
l_Lake_mkBuildContext___closed__1 = _init_l_Lake_mkBuildContext___closed__1();
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
l_Lake_mkBuildContext___closed__7 = _init_l_Lake_mkBuildContext___closed__7();
lean_mark_persistent(l_Lake_mkBuildContext___closed__7);
l_Lake_mkBuildContext___closed__8 = _init_l_Lake_mkBuildContext___closed__8();
lean_mark_persistent(l_Lake_mkBuildContext___closed__8);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames);
l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0);
l___private_Lake_Build_Run_0__Lake_Ansi_resetLine = _init_l___private_Lake_Build_Run_0__Lake_Ansi_resetLine();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__3 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__4 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__5 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__5();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__5);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__7 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__7();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__8 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__8();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__8);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__9 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__9();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__9);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__10 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__10();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__10);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__11 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__11();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__12 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__12();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__13 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__13();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__13);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__14 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__14();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__15 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__15();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__16 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__17 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__18 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__19 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__20 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__21 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__21();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__22 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__22();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__22);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5);
l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6);
l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0);
l_Lake_noBuildCode = _init_l_Lake_noBuildCode();
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
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0);
l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0 = _init_l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__0);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__1);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__2 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__2();
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__3);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__4 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__4();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__4);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__5 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__5();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__5);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__6 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__6();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__6);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__7);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__8 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__8();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__8);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__9 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__9();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__9);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__10 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__10();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__10);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__11);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__12 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__12();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__12);
l_Lake_Workspace_runFetchM___redArg___lam__2___closed__13 = _init_l_Lake_Workspace_runFetchM___redArg___lam__2___closed__13();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___lam__2___closed__13);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
