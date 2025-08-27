// Lean compiler output
// Module: Lake.Build.Run
// Imports: Lake.Config.Workspace Lake.Config.Monad Lake.Build.Job.Monad Lake.Build.Index
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
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx___boxed(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_save(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7;
uint8_t l_Lake_instDecidableEqJobAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8;
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static uint64_t l_Lake_mkBuildContext___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__28;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__20;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__13;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static uint8_t l_Lake_Workspace_runFetchM___redArg___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
static lean_object* l_Lake_mkBuildContext___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__17;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Package_inputsFileIn(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__4;
static lean_object* l_Lake_mkBuildContext___closed__7;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_saveInputs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
uint8_t lean_strict_and(uint8_t, uint8_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__6;
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__16;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__5;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__19;
lean_object* lean_io_mono_ms_now(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__6;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__14;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0;
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__0;
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__11;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lake_Cache_isDisabled(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__23;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__9;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__27;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__18;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__7;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__24;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__12;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
lean_object* lean_task_get_own(lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__5;
LEAN_EXPORT lean_object* l_Lake_MonitorResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__21;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_mkBuildContext___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__25;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__26;
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorState_ctorIdx(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__13;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object*, lean_object*);
uint8_t l_Lake_ordJobAction____x40_Lake_Build_Job_Basic_1212199115____hygCtx___hyg_24_(uint8_t, uint8_t);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_ctorIdx(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
extern lean_object* l_Lean_versionStringCore;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__15;
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__14;
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__10;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorResult_ctorIdx(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__4;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1;
static lean_object* l_Lake_mkBuildContext___closed__8;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_24_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__8;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__10;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___redArg___closed__22;
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
x_9 = l_Lake_Env_leanGithash(x_8);
x_10 = l_Lake_mkBuildContext___closed__1;
x_11 = lean_string_hash(x_9);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = l_Lake_mkBuildContext___closed__6;
x_14 = lean_string_append(x_13, x_9);
lean_dec_ref(x_9);
x_15 = l_Lake_mkBuildContext___closed__8;
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
x_21 = l_Lake_Env_leanGithash(x_20);
x_22 = l_Lake_mkBuildContext___closed__1;
x_23 = lean_string_hash(x_21);
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = l_Lake_mkBuildContext___closed__6;
x_26 = lean_string_append(x_25, x_21);
lean_dec_ref(x_21);
x_27 = l_Lake_mkBuildContext___closed__8;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_3, x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_4, x_2, x_3, x_5);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_13 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_14 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_15 = lean_unsigned_to_nat(84u);
x_16 = lean_unsigned_to_nat(4u);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_19 = lean_io_error_to_string(x_10);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_String_quote(x_2);
lean_dec_ref(x_2);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_26 = lean_format_pretty(x_24, x_25, x_17, x_17);
x_27 = lean_string_append(x_22, x_26);
lean_dec_ref(x_26);
x_28 = l_mkPanicMessageWithDecl(x_13, x_14, x_15, x_16, x_27);
lean_dec_ref(x_27);
x_29 = l_panic___redArg(x_12, x_28);
x_30 = lean_apply_1(x_29, x_11);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_17 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_18 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_19 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_20 = lean_unsigned_to_nat(84u);
x_21 = lean_unsigned_to_nat(4u);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_24 = lean_io_error_to_string(x_15);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_String_quote(x_1);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_31 = lean_format_pretty(x_29, x_30, x_22, x_22);
x_32 = lean_string_append(x_27, x_31);
lean_dec_ref(x_31);
x_33 = l_mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_32);
lean_dec_ref(x_32);
x_34 = l_panic___redArg(x_17, x_33);
x_35 = lean_apply_1(x_34, x_16);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, x_2);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; lean_object* x_38; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_3);
x_18 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_19 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
x_20 = lean_array_fget(x_18, x_16);
x_21 = lean_unbox_uint32(x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Fin_add(x_19, x_16, x_22);
lean_dec(x_16);
x_24 = l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
lean_inc(x_14);
lean_inc(x_13);
lean_ctor_set(x_4, 5, x_23);
lean_ctor_set(x_4, 3, x_24);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_get_size(x_1);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_82);
x_84 = lean_array_get_size(x_2);
x_85 = lean_nat_sub(x_84, x_22);
lean_dec(x_84);
x_86 = lean_array_fget_borrowed(x_2, x_85);
lean_dec(x_85);
x_87 = lean_ctor_get(x_86, 2);
x_88 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_89 = lean_string_append(x_88, x_87);
x_38 = x_89;
goto block_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_nat_sub(x_82, x_22);
lean_dec(x_82);
x_91 = lean_array_fget_borrowed(x_1, x_90);
x_92 = lean_ctor_get(x_91, 2);
x_93 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_94 = lean_string_append(x_93, x_92);
x_95 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_Nat_reprFast(x_90);
x_98 = lean_string_append(x_96, x_97);
lean_dec_ref(x_97);
x_99 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
x_100 = lean_string_append(x_98, x_99);
x_38 = x_100;
goto block_80;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
block_37:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_17);
x_32 = lean_apply_1(x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_25 = x_33;
x_26 = x_34;
goto block_29;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_box(0);
x_25 = x_36;
x_26 = x_35;
goto block_29;
}
}
block_80:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_17, 4);
x_40 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_41 = lean_string_push(x_40, x_21);
x_42 = lean_string_append(x_15, x_41);
lean_dec_ref(x_41);
x_43 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Nat_reprFast(x_13);
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_Nat_reprFast(x_14);
x_50 = lean_string_append(x_48, x_49);
lean_dec_ref(x_49);
x_51 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_38);
lean_dec_ref(x_38);
lean_inc_ref(x_39);
lean_inc_ref(x_53);
x_54 = lean_apply_2(x_39, x_53, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
lean_dec_ref(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_30 = x_55;
goto block_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec_ref(x_54);
x_58 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_59 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_60 = lean_unsigned_to_nat(84u);
x_61 = lean_unsigned_to_nat(4u);
x_62 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_63 = lean_unsigned_to_nat(0u);
x_64 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_65 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_64, x_11);
x_66 = lean_string_append(x_62, x_65);
lean_dec_ref(x_65);
x_67 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_io_error_to_string(x_56);
x_70 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_71 = lean_string_append(x_70, x_51);
x_72 = l_String_quote(x_53);
lean_dec_ref(x_53);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_75 = lean_format_pretty(x_73, x_74, x_63, x_63);
x_76 = lean_string_append(x_71, x_75);
lean_dec_ref(x_75);
x_77 = l_mkPanicMessageWithDecl(x_58, x_59, x_60, x_61, x_76);
lean_dec_ref(x_76);
x_78 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_77, x_57);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_30 = x_79;
goto block_37;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint32_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_122; lean_object* x_130; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_101 = lean_ctor_get(x_4, 0);
x_102 = lean_ctor_get(x_4, 1);
x_103 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_104 = lean_ctor_get(x_4, 2);
x_105 = lean_ctor_get(x_4, 3);
x_106 = lean_ctor_get(x_4, 4);
x_107 = lean_ctor_get(x_4, 5);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_4);
x_108 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_108);
lean_dec_ref(x_3);
x_109 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_110 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
x_111 = lean_array_fget(x_109, x_107);
x_112 = lean_unbox_uint32(x_111);
lean_dec(x_111);
x_113 = lean_unsigned_to_nat(1u);
x_114 = l_Fin_add(x_110, x_107, x_113);
lean_dec(x_107);
x_115 = l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
lean_inc(x_102);
lean_inc(x_101);
x_116 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_116, 0, x_101);
lean_ctor_set(x_116, 1, x_102);
lean_ctor_set(x_116, 2, x_104);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_116, 4, x_106);
lean_ctor_set(x_116, 5, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*6, x_103);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_array_get_size(x_1);
x_175 = lean_nat_dec_lt(x_173, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_174);
x_176 = lean_array_get_size(x_2);
x_177 = lean_nat_sub(x_176, x_113);
lean_dec(x_176);
x_178 = lean_array_fget_borrowed(x_2, x_177);
lean_dec(x_177);
x_179 = lean_ctor_get(x_178, 2);
x_180 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_181 = lean_string_append(x_180, x_179);
x_130 = x_181;
goto block_172;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_182 = lean_nat_sub(x_174, x_113);
lean_dec(x_174);
x_183 = lean_array_fget_borrowed(x_1, x_182);
x_184 = lean_ctor_get(x_183, 2);
x_185 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
x_186 = lean_string_append(x_185, x_184);
x_187 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
x_188 = lean_string_append(x_186, x_187);
x_189 = l_Nat_reprFast(x_182);
x_190 = lean_string_append(x_188, x_189);
lean_dec_ref(x_189);
x_191 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
x_192 = lean_string_append(x_190, x_191);
x_130 = x_192;
goto block_172;
}
block_121:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
block_129:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_123);
lean_dec_ref(x_108);
x_124 = lean_apply_1(x_123, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_117 = x_125;
x_118 = x_126;
goto block_121;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec_ref(x_124);
x_128 = lean_box(0);
x_117 = x_128;
x_118 = x_127;
goto block_121;
}
}
block_172:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_131 = lean_ctor_get(x_108, 4);
x_132 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_133 = lean_string_push(x_132, x_112);
x_134 = lean_string_append(x_105, x_133);
lean_dec_ref(x_133);
x_135 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
x_136 = lean_string_append(x_134, x_135);
x_137 = l_Nat_reprFast(x_101);
x_138 = lean_string_append(x_136, x_137);
lean_dec_ref(x_137);
x_139 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
x_140 = lean_string_append(x_138, x_139);
x_141 = l_Nat_reprFast(x_102);
x_142 = lean_string_append(x_140, x_141);
lean_dec_ref(x_141);
x_143 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_130);
lean_dec_ref(x_130);
lean_inc_ref(x_131);
lean_inc_ref(x_145);
x_146 = lean_apply_2(x_131, x_145, x_5);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
lean_dec_ref(x_145);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
x_122 = x_147;
goto block_129;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec_ref(x_146);
x_150 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_151 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_152 = lean_unsigned_to_nat(84u);
x_153 = lean_unsigned_to_nat(4u);
x_154 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_155 = lean_unsigned_to_nat(0u);
x_156 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_157 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_156, x_11);
x_158 = lean_string_append(x_154, x_157);
lean_dec_ref(x_157);
x_159 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_160 = lean_string_append(x_158, x_159);
x_161 = lean_io_error_to_string(x_148);
x_162 = lean_string_append(x_160, x_161);
lean_dec_ref(x_161);
x_163 = lean_string_append(x_162, x_143);
x_164 = l_String_quote(x_145);
lean_dec_ref(x_145);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_167 = lean_format_pretty(x_165, x_166, x_155, x_155);
x_168 = lean_string_append(x_163, x_167);
lean_dec_ref(x_167);
x_169 = l_mkPanicMessageWithDecl(x_150, x_151, x_152, x_153, x_168);
lean_dec_ref(x_168);
x_170 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_169, x_149);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
x_122 = x_171;
goto block_129;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_178; lean_object* x_179; uint8_t x_180; uint32_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint32_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint32_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint32_t x_265; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; uint8_t x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; uint8_t x_305; uint8_t x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; uint8_t x_331; uint8_t x_332; lean_object* x_333; uint8_t x_334; uint8_t x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; uint8_t x_354; uint8_t x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; uint8_t x_366; lean_object* x_372; lean_object* x_385; lean_object* x_386; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
x_34 = lean_ctor_get(x_3, 5);
x_35 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_35);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_178 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_179);
x_180 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_385 = lean_task_get_own(x_178);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec_ref(x_385);
x_372 = x_386;
goto block_384;
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
lean_inc_ref(x_20);
lean_dec_ref(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = lean_apply_1(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
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
lean_dec_ref(x_22);
x_26 = lean_box(0);
x_11 = x_18;
x_12 = x_26;
x_13 = x_25;
goto block_16;
}
}
block_59:
{
uint8_t x_50; 
x_50 = lean_nat_dec_lt(x_45, x_48);
lean_dec(x_45);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_43);
lean_dec_ref(x_35);
x_17 = x_44;
x_18 = x_46;
x_19 = x_47;
goto block_27;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec_ref(x_43);
lean_dec_ref(x_35);
x_17 = x_44;
x_18 = x_46;
x_19 = x_47;
goto block_27;
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_box(0);
x_53 = 0;
x_54 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_35, x_49, x_40, x_43, x_53, x_54, x_52, x_46, x_47);
lean_dec_ref(x_43);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_17 = x_44;
x_18 = x_58;
x_19 = x_57;
goto block_27;
}
}
}
block_69:
{
if (x_64 == 0)
{
lean_dec(x_66);
lean_dec(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_35);
x_17 = x_61;
x_18 = x_63;
x_19 = x_67;
goto block_27;
}
else
{
if (x_65 == 0)
{
x_43 = x_60;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_67;
x_48 = x_66;
x_49 = x_36;
goto block_59;
}
else
{
uint8_t x_68; 
x_68 = 0;
x_43 = x_60;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_67;
x_48 = x_66;
x_49 = x_68;
goto block_59;
}
}
}
block_163:
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_71, 1);
x_83 = lean_ctor_get(x_73, 3);
x_84 = lean_ctor_get(x_82, 4);
lean_ctor_set(x_73, 3, x_77);
x_85 = lean_string_append(x_83, x_80);
lean_dec_ref(x_80);
x_86 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
x_87 = lean_string_append(x_85, x_86);
lean_inc_ref(x_84);
lean_inc_ref(x_87);
x_88 = lean_apply_2(x_84, x_87, x_76);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec_ref(x_88);
x_60 = x_70;
x_61 = x_71;
x_62 = x_72;
x_63 = x_73;
x_64 = x_75;
x_65 = x_79;
x_66 = x_78;
x_67 = x_89;
goto block_69;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec_ref(x_88);
x_92 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_93 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_94 = lean_unsigned_to_nat(84u);
x_95 = lean_unsigned_to_nat(4u);
x_96 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_97 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_98 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_72);
x_99 = l_Lean_Name_num___override(x_98, x_72);
x_100 = l_Lean_Name_str___override(x_99, x_97);
x_101 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_102 = l_Lean_Name_str___override(x_100, x_101);
x_103 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_102, x_74);
x_104 = lean_string_append(x_96, x_103);
lean_dec_ref(x_103);
x_105 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_io_error_to_string(x_90);
x_108 = lean_string_append(x_106, x_107);
lean_dec_ref(x_107);
x_109 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_110 = lean_string_append(x_108, x_109);
x_111 = l_String_quote(x_87);
lean_dec_ref(x_87);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc_n(x_72, 2);
x_114 = lean_format_pretty(x_112, x_113, x_72, x_72);
x_115 = lean_string_append(x_110, x_114);
lean_dec_ref(x_114);
x_116 = l_mkPanicMessageWithDecl(x_92, x_93, x_94, x_95, x_115);
lean_dec_ref(x_115);
x_117 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_116, x_91);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_60 = x_70;
x_61 = x_71;
x_62 = x_72;
x_63 = x_73;
x_64 = x_75;
x_65 = x_79;
x_66 = x_78;
x_67 = x_118;
goto block_69;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_119 = lean_ctor_get(x_71, 1);
x_120 = lean_ctor_get(x_73, 0);
x_121 = lean_ctor_get(x_73, 1);
x_122 = lean_ctor_get_uint8(x_73, sizeof(void*)*6);
x_123 = lean_ctor_get(x_73, 2);
x_124 = lean_ctor_get(x_73, 3);
x_125 = lean_ctor_get(x_73, 4);
x_126 = lean_ctor_get(x_73, 5);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_73);
x_127 = lean_ctor_get(x_119, 4);
x_128 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set(x_128, 1, x_121);
lean_ctor_set(x_128, 2, x_123);
lean_ctor_set(x_128, 3, x_77);
lean_ctor_set(x_128, 4, x_125);
lean_ctor_set(x_128, 5, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*6, x_122);
x_129 = lean_string_append(x_124, x_80);
lean_dec_ref(x_80);
x_130 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
x_131 = lean_string_append(x_129, x_130);
lean_inc_ref(x_127);
lean_inc_ref(x_131);
x_132 = lean_apply_2(x_127, x_131, x_76);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_dec_ref(x_131);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec_ref(x_132);
x_60 = x_70;
x_61 = x_71;
x_62 = x_72;
x_63 = x_128;
x_64 = x_75;
x_65 = x_79;
x_66 = x_78;
x_67 = x_133;
goto block_69;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec_ref(x_132);
x_136 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_137 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_138 = lean_unsigned_to_nat(84u);
x_139 = lean_unsigned_to_nat(4u);
x_140 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_141 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__7;
x_142 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__12;
lean_inc(x_72);
x_143 = l_Lean_Name_num___override(x_142, x_72);
x_144 = l_Lean_Name_str___override(x_143, x_141);
x_145 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
x_146 = l_Lean_Name_str___override(x_144, x_145);
x_147 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_146, x_74);
x_148 = lean_string_append(x_140, x_147);
lean_dec_ref(x_147);
x_149 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_150 = lean_string_append(x_148, x_149);
x_151 = lean_io_error_to_string(x_134);
x_152 = lean_string_append(x_150, x_151);
lean_dec_ref(x_151);
x_153 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_154 = lean_string_append(x_152, x_153);
x_155 = l_String_quote(x_131);
lean_dec_ref(x_131);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
lean_inc_n(x_72, 2);
x_158 = lean_format_pretty(x_156, x_157, x_72, x_72);
x_159 = lean_string_append(x_154, x_158);
lean_dec_ref(x_158);
x_160 = l_mkPanicMessageWithDecl(x_136, x_137, x_138, x_139, x_159);
lean_dec_ref(x_159);
x_161 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_160, x_135);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec_ref(x_161);
x_60 = x_70;
x_61 = x_71;
x_62 = x_72;
x_63 = x_128;
x_64 = x_75;
x_65 = x_79;
x_66 = x_78;
x_67 = x_162;
goto block_69;
}
}
}
block_177:
{
lean_object* x_176; 
x_176 = l_Lake_Ansi_chalk(x_175, x_172);
lean_dec_ref(x_172);
lean_dec_ref(x_175);
x_70 = x_164;
x_71 = x_165;
x_72 = x_167;
x_73 = x_166;
x_74 = x_168;
x_75 = x_169;
x_76 = x_171;
x_77 = x_170;
x_78 = x_174;
x_79 = x_173;
x_80 = x_176;
goto block_163;
}
block_216:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_195 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_196 = lean_string_push(x_195, x_181);
x_197 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
x_198 = lean_string_append(x_196, x_197);
x_199 = l_Nat_reprFast(x_28);
x_200 = lean_string_append(x_198, x_199);
lean_dec_ref(x_199);
x_201 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
x_202 = lean_string_append(x_200, x_201);
x_203 = l_Nat_reprFast(x_29);
x_204 = lean_string_append(x_202, x_203);
lean_dec_ref(x_203);
x_205 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1;
x_206 = lean_string_append(x_204, x_205);
x_207 = lean_string_append(x_206, x_189);
lean_dec_ref(x_189);
x_208 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2;
x_209 = lean_string_append(x_207, x_208);
x_210 = lean_string_append(x_209, x_191);
lean_dec_ref(x_191);
x_211 = lean_string_append(x_210, x_208);
x_212 = lean_string_append(x_211, x_179);
lean_dec_ref(x_179);
x_213 = lean_string_append(x_212, x_194);
lean_dec_ref(x_194);
if (x_40 == 0)
{
x_70 = x_182;
x_71 = x_188;
x_72 = x_183;
x_73 = x_184;
x_74 = x_185;
x_75 = x_186;
x_76 = x_192;
x_77 = x_195;
x_78 = x_193;
x_79 = x_187;
x_80 = x_213;
goto block_163;
}
else
{
if (x_186 == 0)
{
lean_object* x_214; 
x_214 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3;
x_164 = x_182;
x_165 = x_188;
x_166 = x_184;
x_167 = x_183;
x_168 = x_185;
x_169 = x_186;
x_170 = x_195;
x_171 = x_192;
x_172 = x_213;
x_173 = x_187;
x_174 = x_193;
x_175 = x_214;
goto block_177;
}
else
{
lean_object* x_215; 
x_215 = l_Lake_LogLevel_ansiColor(x_190);
x_164 = x_182;
x_165 = x_188;
x_166 = x_184;
x_167 = x_183;
x_168 = x_185;
x_169 = x_186;
x_170 = x_195;
x_171 = x_192;
x_172 = x_213;
x_173 = x_187;
x_174 = x_193;
x_175 = x_215;
goto block_177;
}
}
}
block_231:
{
lean_object* x_230; 
x_230 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_181 = x_217;
x_182 = x_218;
x_183 = x_219;
x_184 = x_220;
x_185 = x_221;
x_186 = x_222;
x_187 = x_223;
x_188 = x_224;
x_189 = x_225;
x_190 = x_226;
x_191 = x_227;
x_192 = x_228;
x_193 = x_229;
x_194 = x_230;
goto block_216;
}
block_252:
{
if (x_42 == 0)
{
lean_dec(x_241);
x_217 = x_232;
x_218 = x_233;
x_219 = x_234;
x_220 = x_235;
x_221 = x_236;
x_222 = x_237;
x_223 = x_238;
x_224 = x_239;
x_225 = x_245;
x_226 = x_240;
x_227 = x_242;
x_228 = x_243;
x_229 = x_244;
goto block_231;
}
else
{
uint8_t x_246; 
x_246 = lean_nat_dec_lt(x_234, x_241);
if (x_246 == 0)
{
lean_dec(x_241);
x_217 = x_232;
x_218 = x_233;
x_219 = x_234;
x_220 = x_235;
x_221 = x_236;
x_222 = x_237;
x_223 = x_238;
x_224 = x_239;
x_225 = x_245;
x_226 = x_240;
x_227 = x_242;
x_228 = x_243;
x_229 = x_244;
goto block_231;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4;
x_248 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(x_241);
x_249 = lean_string_append(x_247, x_248);
lean_dec_ref(x_248);
x_250 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5;
x_251 = lean_string_append(x_249, x_250);
x_181 = x_232;
x_182 = x_233;
x_183 = x_234;
x_184 = x_235;
x_185 = x_236;
x_186 = x_237;
x_187 = x_238;
x_188 = x_239;
x_189 = x_245;
x_190 = x_240;
x_191 = x_242;
x_192 = x_243;
x_193 = x_244;
x_194 = x_251;
goto block_216;
}
}
}
block_268:
{
if (x_180 == 0)
{
lean_object* x_266; 
x_266 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_232 = x_265;
x_233 = x_253;
x_234 = x_256;
x_235 = x_255;
x_236 = x_259;
x_237 = x_261;
x_238 = x_264;
x_239 = x_254;
x_240 = x_257;
x_241 = x_258;
x_242 = x_260;
x_243 = x_262;
x_244 = x_263;
x_245 = x_266;
goto block_252;
}
else
{
lean_object* x_267; 
x_267 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6;
x_232 = x_265;
x_233 = x_253;
x_234 = x_256;
x_235 = x_255;
x_236 = x_259;
x_237 = x_261;
x_238 = x_264;
x_239 = x_254;
x_240 = x_257;
x_241 = x_258;
x_242 = x_260;
x_243 = x_262;
x_244 = x_263;
x_245 = x_267;
goto block_252;
}
}
block_285:
{
if (x_277 == 0)
{
if (x_41 == 0)
{
lean_dec(x_280);
lean_dec(x_274);
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec_ref(x_269);
lean_dec_ref(x_179);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_272;
x_6 = x_278;
goto block_10;
}
else
{
if (x_40 == 0)
{
if (x_276 == 0)
{
lean_dec(x_280);
lean_dec(x_274);
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec_ref(x_269);
lean_dec_ref(x_179);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_272;
x_6 = x_278;
goto block_10;
}
else
{
lean_object* x_281; uint32_t x_282; 
x_281 = l_Lake_JobAction_verb(x_279, x_275);
x_282 = 10004;
x_253 = x_269;
x_254 = x_270;
x_255 = x_272;
x_256 = x_271;
x_257 = x_273;
x_258 = x_274;
x_259 = x_276;
x_260 = x_281;
x_261 = x_277;
x_262 = x_278;
x_263 = x_280;
x_264 = x_279;
x_265 = x_282;
goto block_268;
}
}
else
{
lean_dec(x_280);
lean_dec(x_274);
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec_ref(x_269);
lean_dec_ref(x_179);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_272;
x_6 = x_278;
goto block_10;
}
}
}
else
{
lean_object* x_283; uint32_t x_284; 
x_283 = l_Lake_JobAction_verb(x_279, x_275);
x_284 = l_Lake_LogLevel_icon(x_273);
x_253 = x_269;
x_254 = x_270;
x_255 = x_272;
x_256 = x_271;
x_257 = x_273;
x_258 = x_274;
x_259 = x_277;
x_260 = x_283;
x_261 = x_277;
x_262 = x_278;
x_263 = x_280;
x_264 = x_279;
x_265 = x_284;
goto block_268;
}
}
block_298:
{
if (x_180 == 0)
{
x_269 = x_286;
x_270 = x_287;
x_271 = x_289;
x_272 = x_288;
x_273 = x_290;
x_274 = x_291;
x_275 = x_292;
x_276 = x_293;
x_277 = x_297;
x_278 = x_294;
x_279 = x_295;
x_280 = x_296;
goto block_285;
}
else
{
if (x_39 == 0)
{
lean_dec(x_296);
lean_dec(x_291);
lean_dec(x_289);
lean_dec_ref(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_179);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_288;
x_6 = x_294;
goto block_10;
}
else
{
x_269 = x_286;
x_270 = x_287;
x_271 = x_289;
x_272 = x_288;
x_273 = x_290;
x_274 = x_291;
x_275 = x_292;
x_276 = x_293;
x_277 = x_297;
x_278 = x_294;
x_279 = x_295;
x_280 = x_296;
goto block_285;
}
}
}
block_324:
{
if (x_308 == 0)
{
if (x_299 == 0)
{
x_286 = x_300;
x_287 = x_309;
x_288 = x_310;
x_289 = x_302;
x_290 = x_303;
x_291 = x_304;
x_292 = x_305;
x_293 = x_306;
x_294 = x_311;
x_295 = x_308;
x_296 = x_307;
x_297 = x_299;
goto block_298;
}
else
{
x_286 = x_300;
x_287 = x_309;
x_288 = x_310;
x_289 = x_302;
x_290 = x_303;
x_291 = x_304;
x_292 = x_305;
x_293 = x_306;
x_294 = x_311;
x_295 = x_308;
x_296 = x_307;
x_297 = x_301;
goto block_298;
}
}
else
{
if (x_180 == 0)
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_310);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_310, 2);
lean_inc_ref(x_179);
x_314 = lean_array_push(x_313, x_179);
lean_ctor_set(x_310, 2, x_314);
x_286 = x_300;
x_287 = x_309;
x_288 = x_310;
x_289 = x_302;
x_290 = x_303;
x_291 = x_304;
x_292 = x_305;
x_293 = x_306;
x_294 = x_311;
x_295 = x_308;
x_296 = x_307;
x_297 = x_308;
goto block_298;
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_315 = lean_ctor_get(x_310, 0);
x_316 = lean_ctor_get(x_310, 1);
x_317 = lean_ctor_get_uint8(x_310, sizeof(void*)*6);
x_318 = lean_ctor_get(x_310, 2);
x_319 = lean_ctor_get(x_310, 3);
x_320 = lean_ctor_get(x_310, 4);
x_321 = lean_ctor_get(x_310, 5);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_310);
lean_inc_ref(x_179);
x_322 = lean_array_push(x_318, x_179);
x_323 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_323, 0, x_315);
lean_ctor_set(x_323, 1, x_316);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set(x_323, 4, x_320);
lean_ctor_set(x_323, 5, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*6, x_317);
x_286 = x_300;
x_287 = x_309;
x_288 = x_323;
x_289 = x_302;
x_290 = x_303;
x_291 = x_304;
x_292 = x_305;
x_293 = x_306;
x_294 = x_311;
x_295 = x_308;
x_296 = x_307;
x_297 = x_308;
goto block_298;
}
}
else
{
x_286 = x_300;
x_287 = x_309;
x_288 = x_310;
x_289 = x_302;
x_290 = x_303;
x_291 = x_304;
x_292 = x_305;
x_293 = x_306;
x_294 = x_311;
x_295 = x_308;
x_296 = x_307;
x_297 = x_308;
goto block_298;
}
}
}
block_345:
{
if (x_30 == 0)
{
uint8_t x_335; uint8_t x_336; 
x_335 = 3;
x_336 = l_Lake_instDecidableEqJobAction(x_331, x_335);
if (x_336 == 0)
{
x_299 = x_325;
x_300 = x_326;
x_301 = x_327;
x_302 = x_328;
x_303 = x_329;
x_304 = x_330;
x_305 = x_331;
x_306 = x_334;
x_307 = x_333;
x_308 = x_332;
x_309 = x_2;
x_310 = x_3;
x_311 = x_4;
goto block_324;
}
else
{
uint8_t x_337; 
lean_inc(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_31);
x_337 = !lean_is_exclusive(x_3);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_338 = lean_ctor_get(x_3, 5);
lean_dec(x_338);
x_339 = lean_ctor_get(x_3, 4);
lean_dec(x_339);
x_340 = lean_ctor_get(x_3, 3);
lean_dec(x_340);
x_341 = lean_ctor_get(x_3, 2);
lean_dec(x_341);
x_342 = lean_ctor_get(x_3, 1);
lean_dec(x_342);
x_343 = lean_ctor_get(x_3, 0);
lean_dec(x_343);
lean_inc(x_29);
lean_inc(x_28);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_336);
x_299 = x_325;
x_300 = x_326;
x_301 = x_327;
x_302 = x_328;
x_303 = x_329;
x_304 = x_330;
x_305 = x_331;
x_306 = x_334;
x_307 = x_333;
x_308 = x_332;
x_309 = x_2;
x_310 = x_3;
x_311 = x_4;
goto block_324;
}
else
{
lean_object* x_344; 
lean_dec(x_3);
lean_inc(x_29);
lean_inc(x_28);
x_344 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_344, 0, x_28);
lean_ctor_set(x_344, 1, x_29);
lean_ctor_set(x_344, 2, x_31);
lean_ctor_set(x_344, 3, x_32);
lean_ctor_set(x_344, 4, x_33);
lean_ctor_set(x_344, 5, x_34);
lean_ctor_set_uint8(x_344, sizeof(void*)*6, x_336);
x_299 = x_325;
x_300 = x_326;
x_301 = x_327;
x_302 = x_328;
x_303 = x_329;
x_304 = x_330;
x_305 = x_331;
x_306 = x_334;
x_307 = x_333;
x_308 = x_332;
x_309 = x_2;
x_310 = x_344;
x_311 = x_4;
goto block_324;
}
}
}
else
{
x_299 = x_325;
x_300 = x_326;
x_301 = x_327;
x_302 = x_328;
x_303 = x_329;
x_304 = x_330;
x_305 = x_331;
x_306 = x_334;
x_307 = x_333;
x_308 = x_332;
x_309 = x_2;
x_310 = x_3;
x_311 = x_4;
goto block_324;
}
}
block_358:
{
uint8_t x_355; 
x_355 = l_Lake_ordJobAction____x40_Lake_Build_Job_Basic_1212199115____hygCtx___hyg_24_(x_38, x_351);
if (x_355 == 2)
{
uint8_t x_356; 
x_356 = 0;
x_325 = x_346;
x_326 = x_347;
x_327 = x_354;
x_328 = x_348;
x_329 = x_349;
x_330 = x_350;
x_331 = x_351;
x_332 = x_353;
x_333 = x_352;
x_334 = x_356;
goto block_345;
}
else
{
uint8_t x_357; 
x_357 = 1;
x_325 = x_346;
x_326 = x_347;
x_327 = x_354;
x_328 = x_348;
x_329 = x_349;
x_330 = x_350;
x_331 = x_351;
x_332 = x_353;
x_333 = x_352;
x_334 = x_357;
goto block_345;
}
}
block_371:
{
uint8_t x_367; uint8_t x_368; 
x_367 = lean_strict_and(x_359, x_366);
x_368 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_24_(x_36, x_362);
if (x_368 == 2)
{
uint8_t x_369; 
x_369 = 0;
x_346 = x_359;
x_347 = x_360;
x_348 = x_361;
x_349 = x_362;
x_350 = x_363;
x_351 = x_364;
x_352 = x_365;
x_353 = x_367;
x_354 = x_369;
goto block_358;
}
else
{
uint8_t x_370; 
x_370 = 1;
x_346 = x_359;
x_347 = x_360;
x_348 = x_361;
x_349 = x_362;
x_350 = x_363;
x_351 = x_364;
x_352 = x_365;
x_353 = x_367;
x_354 = x_370;
goto block_358;
}
}
block_384:
{
lean_object* x_373; uint8_t x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; uint8_t x_380; uint8_t x_381; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc_ref(x_373);
x_374 = lean_ctor_get_uint8(x_372, sizeof(void*)*3);
x_375 = lean_ctor_get(x_372, 2);
lean_inc(x_375);
lean_dec_ref(x_372);
x_376 = l_Lake_Log_maxLv(x_373);
x_377 = lean_array_get_size(x_373);
x_378 = lean_unsigned_to_nat(0u);
x_379 = lean_nat_dec_eq(x_377, x_378);
x_380 = l_instDecidableNot___redArg(x_379);
x_381 = l_Lake_ordLogLevel____x40_Lake_Util_Log_328358094____hygCtx___hyg_24_(x_37, x_376);
if (x_381 == 2)
{
uint8_t x_382; 
x_382 = 0;
x_359 = x_380;
x_360 = x_373;
x_361 = x_378;
x_362 = x_376;
x_363 = x_375;
x_364 = x_374;
x_365 = x_377;
x_366 = x_382;
goto block_371;
}
else
{
uint8_t x_383; 
x_383 = 1;
x_359 = x_380;
x_360 = x_373;
x_361 = x_378;
x_362 = x_376;
x_363 = x_375;
x_364 = x_374;
x_365 = x_377;
x_366 = x_383;
goto block_371;
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_1, x_10, x_11, x_4, x_12, x_13, x_7, x_8, x_9);
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
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
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
lean_inc(x_17);
lean_inc(x_16);
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
lean_inc(x_17);
lean_inc(x_16);
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
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec_ref(x_20);
lean_inc_ref(x_5);
x_42 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(x_18, x_5, x_6, x_41);
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
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
x_52 = lean_ctor_get_uint8(x_44, sizeof(void*)*6);
x_53 = lean_ctor_get(x_44, 2);
x_54 = lean_ctor_get(x_44, 3);
x_55 = lean_ctor_get(x_44, 4);
x_56 = lean_ctor_get(x_44, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_50, x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set(x_59, 5, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_52);
x_8 = x_4;
x_9 = x_59;
x_10 = x_45;
goto block_14;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
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
x_30 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
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
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_34, x_35, x_30, x_2, x_3, x_14);
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
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_8, x_25, x_26, x_20, x_2, x_21, x_22);
lean_dec(x_8);
return x_27;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_44 = lean_ctor_get(x_3, 2);
x_45 = lean_ctor_get(x_3, 3);
x_46 = lean_ctor_get(x_3, 4);
x_47 = lean_ctor_get(x_3, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_3);
x_48 = lean_array_get_size(x_8);
x_59 = lean_nat_add(x_42, x_48);
lean_dec(x_42);
x_60 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_60, 0, x_41);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_44);
lean_ctor_set(x_60, 3, x_45);
lean_ctor_set(x_60, 4, x_46);
lean_ctor_set(x_60, 5, x_47);
lean_ctor_set_uint8(x_60, sizeof(void*)*6, x_43);
x_61 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_62 = lean_array_get_size(x_1);
x_63 = lean_nat_dec_lt(x_10, x_62);
if (x_63 == 0)
{
lean_dec(x_62);
lean_inc_ref(x_60);
lean_ctor_set(x_6, 1, x_60);
lean_ctor_set(x_6, 0, x_61);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_6);
x_49 = x_12;
x_50 = x_61;
x_51 = x_60;
x_52 = x_14;
goto block_58;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_62, x_62);
if (x_64 == 0)
{
lean_dec(x_62);
lean_inc_ref(x_60);
lean_ctor_set(x_6, 1, x_60);
lean_ctor_set(x_6, 0, x_61);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_6);
x_49 = x_12;
x_50 = x_61;
x_51 = x_60;
x_52 = x_14;
goto block_58;
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_12);
lean_free_object(x_6);
x_65 = 0;
x_66 = lean_usize_of_nat(x_62);
lean_dec(x_62);
lean_inc_ref(x_2);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_65, x_66, x_61, x_2, x_60, x_14);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_49 = x_67;
x_50 = x_70;
x_51 = x_71;
x_52 = x_69;
goto block_58;
}
}
block_58:
{
uint8_t x_53; 
x_53 = lean_nat_dec_lt(x_10, x_48);
if (x_53 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_48);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_49;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_48, x_48);
if (x_54 == 0)
{
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_48);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_49;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
lean_dec_ref(x_49);
x_55 = 0;
x_56 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_8, x_55, x_56, x_50, x_2, x_51, x_52);
lean_dec(x_8);
return x_57;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_dec(x_12);
x_73 = lean_ctor_get(x_3, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_76 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_3, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 5);
lean_inc(x_79);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_80 = x_3;
} else {
 lean_dec_ref(x_3);
 x_80 = lean_box(0);
}
x_81 = lean_array_get_size(x_8);
x_92 = lean_nat_add(x_74, x_81);
lean_dec(x_74);
if (lean_is_scalar(x_80)) {
 x_93 = lean_alloc_ctor(0, 6, 1);
} else {
 x_93 = x_80;
}
lean_ctor_set(x_93, 0, x_73);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_76);
lean_ctor_set(x_93, 3, x_77);
lean_ctor_set(x_93, 4, x_78);
lean_ctor_set(x_93, 5, x_79);
lean_ctor_set_uint8(x_93, sizeof(void*)*6, x_75);
x_94 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_95 = lean_array_get_size(x_1);
x_96 = lean_nat_dec_lt(x_10, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_95);
lean_inc_ref(x_93);
lean_ctor_set(x_6, 1, x_93);
lean_ctor_set(x_6, 0, x_94);
lean_inc(x_72);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_6);
lean_ctor_set(x_97, 1, x_72);
x_82 = x_97;
x_83 = x_94;
x_84 = x_93;
x_85 = x_72;
goto block_91;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_95, x_95);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_95);
lean_inc_ref(x_93);
lean_ctor_set(x_6, 1, x_93);
lean_ctor_set(x_6, 0, x_94);
lean_inc(x_72);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_6);
lean_ctor_set(x_99, 1, x_72);
x_82 = x_99;
x_83 = x_94;
x_84 = x_93;
x_85 = x_72;
goto block_91;
}
else
{
size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_6);
x_100 = 0;
x_101 = lean_usize_of_nat(x_95);
lean_dec(x_95);
lean_inc_ref(x_2);
x_102 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_100, x_101, x_94, x_2, x_93, x_72);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_82 = x_102;
x_83 = x_105;
x_84 = x_106;
x_85 = x_104;
goto block_91;
}
}
block_91:
{
uint8_t x_86; 
x_86 = lean_nat_dec_lt(x_10, x_81);
if (x_86 == 0)
{
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_81);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_82;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_81, x_81);
if (x_87 == 0)
{
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_81);
lean_dec(x_8);
lean_dec_ref(x_2);
return x_82;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; 
lean_dec_ref(x_82);
x_88 = 0;
x_89 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_90 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_8, x_88, x_89, x_83, x_2, x_84, x_85);
lean_dec(x_8);
return x_90;
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_107 = lean_ctor_get(x_6, 0);
x_108 = lean_ctor_get(x_6, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_6);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lake_mkBuildContext___closed__0;
x_111 = lean_st_ref_set(x_5, x_110, x_108);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_3, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_3, 1);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_117 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_3, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_3, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_121 = x_3;
} else {
 lean_dec_ref(x_3);
 x_121 = lean_box(0);
}
x_122 = lean_array_get_size(x_107);
x_133 = lean_nat_add(x_115, x_122);
lean_dec(x_115);
if (lean_is_scalar(x_121)) {
 x_134 = lean_alloc_ctor(0, 6, 1);
} else {
 x_134 = x_121;
}
lean_ctor_set(x_134, 0, x_114);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_117);
lean_ctor_set(x_134, 3, x_118);
lean_ctor_set(x_134, 4, x_119);
lean_ctor_set(x_134, 5, x_120);
lean_ctor_set_uint8(x_134, sizeof(void*)*6, x_116);
x_135 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_136 = lean_array_get_size(x_1);
x_137 = lean_nat_dec_lt(x_109, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_136);
lean_inc_ref(x_134);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_134);
lean_inc(x_112);
if (lean_is_scalar(x_113)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_113;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_112);
x_123 = x_139;
x_124 = x_135;
x_125 = x_134;
x_126 = x_112;
goto block_132;
}
else
{
uint8_t x_140; 
x_140 = lean_nat_dec_le(x_136, x_136);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_136);
lean_inc_ref(x_134);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_134);
lean_inc(x_112);
if (lean_is_scalar(x_113)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_113;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_112);
x_123 = x_142;
x_124 = x_135;
x_125 = x_134;
x_126 = x_112;
goto block_132;
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_113);
x_143 = 0;
x_144 = lean_usize_of_nat(x_136);
lean_dec(x_136);
lean_inc_ref(x_2);
x_145 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_143, x_144, x_135, x_2, x_134, x_112);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_123 = x_145;
x_124 = x_148;
x_125 = x_149;
x_126 = x_147;
goto block_132;
}
}
block_132:
{
uint8_t x_127; 
x_127 = lean_nat_dec_lt(x_109, x_122);
if (x_127 == 0)
{
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec(x_122);
lean_dec(x_107);
lean_dec_ref(x_2);
return x_123;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_122, x_122);
if (x_128 == 0)
{
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec(x_122);
lean_dec(x_107);
lean_dec_ref(x_2);
return x_123;
}
else
{
size_t x_129; size_t x_130; lean_object* x_131; 
lean_dec_ref(x_123);
x_129 = 0;
x_130 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_131 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_107, x_129, x_130, x_124, x_2, x_125, x_126);
lean_dec(x_107);
return x_131;
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
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_io_mono_ms_now(x_3);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_ctor_get(x_2, 4);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_nat_sub(x_38, x_40);
lean_dec(x_38);
x_43 = lean_nat_sub(x_41, x_42);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_dec(x_43);
x_4 = x_2;
x_5 = x_39;
goto block_36;
}
else
{
uint32_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_uint32_of_nat(x_43);
lean_dec(x_43);
x_47 = l_IO_sleep(x_46, x_39);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_4 = x_2;
x_5 = x_48;
goto block_36;
}
block_36:
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_13);
lean_ctor_set(x_21, 5, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*6, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_28 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_4, 5);
lean_inc(x_30);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_31 = x_4;
} else {
 lean_dec_ref(x_4);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 6, 1);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3, x_4);
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
x_19 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_13, x_14, x_2, x_11, x_9);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_22, x_21);
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
x_35 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_28, x_29, x_2, x_11, x_9);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_38, x_37);
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
x_55 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_46, x_47, x_2, x_45, x_44);
lean_dec(x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_58, x_57);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_loop(x_1, x_2, x_3, x_4);
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
x_13 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_37 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_38 = lean_unsigned_to_nat(84u);
x_39 = lean_unsigned_to_nat(4u);
x_40 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_41 = lean_io_error_to_string(x_34);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_String_quote(x_12);
lean_dec_ref(x_12);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_48 = lean_format_pretty(x_46, x_47, x_20, x_20);
x_49 = lean_string_append(x_44, x_48);
lean_dec_ref(x_48);
x_50 = l_mkPanicMessageWithDecl(x_36, x_37, x_38, x_39, x_49);
lean_dec_ref(x_49);
x_51 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_50, x_35);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_25 = x_52;
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_9);
return x_55;
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
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_56 = lean_ctor_get(x_7, 0);
x_57 = lean_ctor_get(x_7, 1);
x_58 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_59 = lean_ctor_get(x_7, 2);
x_60 = lean_ctor_get(x_7, 3);
x_61 = lean_ctor_get(x_7, 4);
x_62 = lean_ctor_get(x_7, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_7);
x_63 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_64 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_64, 5, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_58);
x_70 = lean_string_utf8_byte_size(x_60);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_eq(x_70, x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_83; 
x_73 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_73);
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_73, 4);
lean_inc_ref(x_75);
lean_dec_ref(x_73);
lean_inc_ref(x_60);
x_83 = lean_apply_2(x_75, x_60, x_9);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_dec_ref(x_60);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_76 = x_84;
goto block_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec_ref(x_83);
x_87 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_88 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_89 = lean_unsigned_to_nat(84u);
x_90 = lean_unsigned_to_nat(4u);
x_91 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_92 = lean_io_error_to_string(x_85);
x_93 = lean_string_append(x_91, x_92);
lean_dec_ref(x_92);
x_94 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_95 = lean_string_append(x_93, x_94);
x_96 = l_String_quote(x_60);
lean_dec_ref(x_60);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_99 = lean_format_pretty(x_97, x_98, x_71, x_71);
x_100 = lean_string_append(x_95, x_99);
lean_dec_ref(x_99);
x_101 = l_mkPanicMessageWithDecl(x_87, x_88, x_89, x_90, x_100);
lean_dec_ref(x_100);
x_102 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_101, x_86);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_76 = x_103;
goto block_82;
}
block_82:
{
lean_object* x_77; 
x_77 = lean_apply_1(x_74, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_65 = x_78;
x_66 = x_79;
goto block_69;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec_ref(x_77);
x_81 = lean_box(0);
x_65 = x_81;
x_66 = x_80;
goto block_69;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_60);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_64);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_9);
return x_106;
}
block_69:
{
lean_object* x_67; lean_object* x_68; 
if (lean_is_scalar(x_8)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_8;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_64);
if (lean_is_scalar(x_10)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_10;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
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
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_io_mono_ms_now(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 4, x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 5, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 6, x_10);
x_19 = lean_unsigned_to_nat(0u);
x_20 = 0;
x_21 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_12);
lean_ctor_set(x_21, 3, x_11);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*6, x_20);
x_22 = l___private_Lake_Build_Run_0__Lake_Monitor_main(x_1, x_18, x_21, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_24, sizeof(void*)*6);
x_29 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_24, sizeof(void*)*6);
x_34 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
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
x_22 = l_Lake_monitorJobs(x_1, x_2, x_3, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_11, x_12, x_13, x_14);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(x_6, x_5, x_17, x_18, x_10, x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_saveInputs_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_10;
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
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_26 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
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
x_42 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_3 = lean_unsigned_to_nat(133u);
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
x_55 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3), 10, 3);
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
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
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
x_40 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(x_39);
x_10 = x_32;
x_11 = x_36;
x_12 = x_33;
x_13 = x_40;
goto block_17;
}
else
{
lean_object* x_41; 
x_41 = lean_string_from_utf8_unchecked(x_37);
lean_dec_ref(x_37);
x_10 = x_32;
x_11 = x_36;
x_12 = x_33;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = lean_apply_2(x_14, x_19, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_7 = x_21;
x_8 = x_22;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
x_25 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_26 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_27 = lean_unsigned_to_nat(84u);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_31 = lean_io_error_to_string(x_23);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_String_quote(x_19);
lean_dec_ref(x_19);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_38 = lean_format_pretty(x_36, x_37, x_29, x_29);
x_39 = lean_string_append(x_34, x_38);
lean_dec_ref(x_38);
x_40 = l_mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_39);
lean_dec_ref(x_39);
x_41 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_40, x_24);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_7 = x_42;
x_8 = x_43;
goto block_12;
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = lean_apply_2(x_14, x_19, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_7 = x_21;
x_8 = x_22;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
x_25 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_26 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_27 = lean_unsigned_to_nat(84u);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_31 = lean_io_error_to_string(x_23);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_String_quote(x_19);
lean_dec_ref(x_19);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_38 = lean_format_pretty(x_36, x_37, x_29, x_29);
x_39 = lean_string_append(x_34, x_38);
lean_dec_ref(x_38);
x_40 = l_mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_39);
lean_dec_ref(x_39);
x_41 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_40, x_24);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_7 = x_42;
x_8 = x_43;
goto block_12;
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
block_12:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(x_1, x_2, x_10, x_4, x_7, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_41 = lean_ctor_get(x_7, 1);
x_42 = lean_ctor_get(x_7, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_39);
lean_dec(x_7);
x_43 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_39, x_8);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
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
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_42);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_40);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 2, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_40);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_29 = l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(x_18, x_30, x_25);
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
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_39 = lean_ctor_get(x_16, 1);
x_40 = lean_ctor_get(x_16, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_16);
x_41 = l_Lake_Workspace_runFetchM___redArg___lam__1___closed__0;
x_42 = l_Substring_takeWhileAux___at___Lake_Workspace_runFetchM_spec__5(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lake_Workspace_runFetchM_spec__6(x_18, x_42, x_25);
x_44 = lean_string_utf8_extract(x_18, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
x_45 = lean_string_append(x_41, x_44);
lean_dec_ref(x_44);
x_46 = 1;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_push(x_37, x_47);
x_49 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set(x_49, 2, x_40);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_38);
x_20 = x_49;
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
uint8_t x_50; 
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_11, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_11, 0, x_55);
return x_11;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_ctor_get(x_12, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_59 = x_12;
} else {
 lean_dec_ref(x_12);
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
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_Workspace_runFetchM___redArg___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 3;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Build completed successfully (", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(").\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("All targets up-to-date (", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" jobs", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1 job", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recFetchWithIndex), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__10;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_Workspace_runFetchM___redArg___closed__11;
x_3 = 0;
x_4 = l_Lake_Workspace_runFetchM___redArg___closed__9;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Some required targets logged failures:\n", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__13;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__15;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("uncaught top-level build failure (this is likely a bug in Lake)", 63, 63);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__17;
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("job computation", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("There were issues saving input mappings to the local artifact cache:\n", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__21;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__22;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__23;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to save input mappings to the local artifact cache.\n", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__25;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___redArg___closed__26;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_3 = l_Lake_Workspace_runFetchM___redArg___closed__27;
x_4 = lean_format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_221; uint8_t x_222; lean_object* x_223; uint8_t x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_242; uint8_t x_243; uint8_t x_312; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 7);
x_21 = l_Lake_OutStream_get(x_13, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_22);
x_30 = l_Lake_AnsiMode_isEnabled(x_22, x_14, x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_33 = l_Lake_mkBuildContext(x_1, x_3, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_box(1);
x_37 = lean_st_mk_ref(x_36, x_35);
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
x_41 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__0), 8, 1);
lean_closure_set(x_41, 0, x_2);
x_42 = lean_unsigned_to_nat(0u);
x_150 = lean_box(0);
x_151 = lean_box(0);
x_152 = l_Lake_Workspace_runFetchM___redArg___closed__8;
x_153 = 1;
x_154 = l_Lake_Workspace_runFetchM___redArg___closed__9;
x_155 = 0;
x_156 = l_Lake_Workspace_runFetchM___redArg___closed__12;
x_157 = lean_box(x_153);
lean_inc(x_34);
lean_inc(x_38);
x_158 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_158, 0, x_41);
lean_closure_set(x_158, 1, x_157);
lean_closure_set(x_158, 2, x_152);
lean_closure_set(x_158, 3, x_151);
lean_closure_set(x_158, 4, x_150);
lean_closure_set(x_158, 5, x_38);
lean_closure_set(x_158, 6, x_34);
lean_closure_set(x_158, 7, x_156);
lean_closure_set(x_158, 8, x_42);
x_159 = lean_io_as_task(x_158, x_42, x_39);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_st_ref_get(x_38, x_161);
lean_dec(x_38);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_box(0);
x_165 = l_Lake_BuildConfig_showProgress(x_3);
lean_dec_ref(x_3);
x_221 = l_Lake_Workspace_runFetchM___redArg___closed__19;
x_222 = 0;
lean_inc(x_160);
x_223 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_223, 0, x_160);
lean_ctor_set(x_223, 1, x_164);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*3, x_222);
x_224 = 2;
x_225 = l_Lake_instDecidableEqVerbosity(x_10, x_224);
if (x_225 == 0)
{
uint8_t x_315; 
x_315 = 2;
x_312 = x_315;
goto block_314;
}
else
{
x_312 = x_155;
goto block_314;
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
block_20:
{
if (x_9 == 0)
{
x_5 = x_17;
goto block_8;
}
else
{
if (x_16 == 0)
{
x_5 = x_17;
goto block_8;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = l_Lake_Workspace_runFetchM___redArg___closed__2;
x_19 = lean_io_exit(x_18, x_17);
return x_19;
}
}
}
block_29:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_26);
lean_dec(x_22);
x_27 = lean_apply_1(x_26, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_16 = x_24;
x_17 = x_28;
goto block_20;
}
block_121:
{
if (x_9 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_47);
lean_dec(x_22);
x_48 = l_Lake_Workspace_runFetchM___redArg___closed__3;
x_49 = lean_string_append(x_48, x_46);
lean_dec_ref(x_46);
x_50 = l_Lake_Workspace_runFetchM___redArg___closed__4;
x_51 = lean_string_append(x_49, x_50);
lean_inc_ref(x_51);
x_52 = lean_apply_2(x_47, x_51, x_43);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec_ref(x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_45);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec_ref(x_52);
x_59 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_60 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_61 = lean_unsigned_to_nat(84u);
x_62 = lean_unsigned_to_nat(4u);
x_63 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_64 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_65 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_64, x_44);
x_66 = lean_string_append(x_63, x_65);
lean_dec_ref(x_65);
x_67 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_io_error_to_string(x_57);
x_70 = lean_string_append(x_68, x_69);
lean_dec_ref(x_69);
x_71 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_72 = lean_string_append(x_70, x_71);
x_73 = l_String_quote(x_51);
lean_dec_ref(x_51);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_76 = lean_format_pretty(x_74, x_75, x_42, x_42);
x_77 = lean_string_append(x_72, x_76);
lean_dec_ref(x_76);
x_78 = l_mkPanicMessageWithDecl(x_59, x_60, x_61, x_62, x_77);
lean_dec_ref(x_77);
x_79 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_78, x_58);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_45);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_45);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_84);
lean_dec(x_22);
x_85 = l_Lake_Workspace_runFetchM___redArg___closed__5;
x_86 = lean_string_append(x_85, x_46);
lean_dec_ref(x_46);
x_87 = l_Lake_Workspace_runFetchM___redArg___closed__4;
x_88 = lean_string_append(x_86, x_87);
lean_inc_ref(x_88);
x_89 = lean_apply_2(x_84, x_88, x_43);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec_ref(x_88);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_45);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_45);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec_ref(x_89);
x_96 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_97 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_98 = lean_unsigned_to_nat(84u);
x_99 = lean_unsigned_to_nat(4u);
x_100 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_101 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_102 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_101, x_9);
x_103 = lean_string_append(x_100, x_102);
lean_dec_ref(x_102);
x_104 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_io_error_to_string(x_94);
x_107 = lean_string_append(x_105, x_106);
lean_dec_ref(x_106);
x_108 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_109 = lean_string_append(x_107, x_108);
x_110 = l_String_quote(x_88);
lean_dec_ref(x_88);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__22;
x_113 = lean_format_pretty(x_111, x_112, x_42, x_42);
x_114 = lean_string_append(x_109, x_113);
lean_dec_ref(x_113);
x_115 = l_mkPanicMessageWithDecl(x_96, x_97, x_98, x_99, x_114);
lean_dec_ref(x_114);
x_116 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_115, x_95);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 0);
lean_dec(x_118);
lean_ctor_set(x_116, 0, x_45);
return x_116;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_45);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
block_133:
{
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_124);
lean_dec(x_22);
if (lean_is_scalar(x_40)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_40;
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_122);
return x_127;
}
else
{
uint8_t x_128; 
lean_dec(x_40);
x_128 = lean_nat_dec_eq(x_124, x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l_Nat_reprFast(x_124);
x_130 = l_Lake_Workspace_runFetchM___redArg___closed__6;
x_131 = lean_string_append(x_129, x_130);
x_43 = x_122;
x_44 = x_126;
x_45 = x_125;
x_46 = x_131;
goto block_121;
}
else
{
lean_object* x_132; 
lean_dec(x_124);
x_132 = l_Lake_Workspace_runFetchM___redArg___closed__7;
x_43 = x_122;
x_44 = x_126;
x_45 = x_125;
x_46 = x_132;
goto block_121;
}
}
}
block_149:
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_array_get_size(x_135);
x_138 = lean_nat_dec_lt(x_42, x_137);
if (x_138 == 0)
{
lean_dec(x_137);
lean_dec_ref(x_135);
x_24 = x_134;
x_25 = x_136;
goto block_29;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_137, x_137);
if (x_139 == 0)
{
lean_dec(x_137);
lean_dec_ref(x_135);
x_24 = x_134;
x_25 = x_136;
goto block_29;
}
else
{
lean_object* x_140; size_t x_141; size_t x_142; lean_object* x_143; 
x_140 = lean_box(0);
x_141 = 0;
x_142 = lean_usize_of_nat(x_137);
lean_dec(x_137);
lean_inc(x_22);
x_143 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(x_22, x_135, x_141, x_142, x_140, x_136);
lean_dec_ref(x_135);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec_ref(x_143);
x_24 = x_134;
x_25 = x_144;
goto block_29;
}
else
{
uint8_t x_145; 
lean_dec(x_22);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
return x_143;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_143, 0);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_143);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
}
block_204:
{
uint8_t x_171; 
x_171 = l_Array_isEmpty___redArg(x_168);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_160);
lean_dec(x_40);
x_172 = lean_ctor_get(x_22, 4);
x_173 = l_Lake_Workspace_runFetchM___redArg___closed__13;
lean_inc_ref(x_172);
x_174 = lean_apply_2(x_172, x_173, x_170);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec_ref(x_174);
x_134 = x_169;
x_135 = x_168;
x_136 = x_175;
goto block_149;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec_ref(x_174);
x_178 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_179 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_180 = lean_unsigned_to_nat(84u);
x_181 = lean_unsigned_to_nat(4u);
x_182 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_183 = lean_io_error_to_string(x_176);
x_184 = lean_string_append(x_182, x_183);
lean_dec_ref(x_183);
x_185 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_186 = lean_string_append(x_184, x_185);
x_187 = l_Lake_Workspace_runFetchM___redArg___closed__16;
x_188 = lean_string_append(x_186, x_187);
x_189 = l_mkPanicMessageWithDecl(x_178, x_179, x_180, x_181, x_188);
lean_dec_ref(x_188);
x_190 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_189, x_177);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec_ref(x_190);
x_134 = x_169;
x_135 = x_168;
x_136 = x_191;
goto block_149;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec_ref(x_168);
x_192 = lean_io_wait(x_160, x_170);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
if (x_165 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec_ref(x_193);
x_122 = x_194;
x_123 = x_166;
x_124 = x_167;
x_125 = x_195;
x_126 = x_165;
goto block_133;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_dec_ref(x_192);
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
lean_dec_ref(x_193);
x_122 = x_196;
x_123 = x_166;
x_124 = x_167;
x_125 = x_197;
x_126 = x_15;
goto block_133;
}
}
else
{
uint8_t x_198; 
lean_dec_ref(x_193);
lean_dec(x_167);
lean_dec(x_40);
lean_dec(x_22);
x_198 = !lean_is_exclusive(x_192);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_192, 0);
lean_dec(x_199);
x_200 = l_Lake_Workspace_runFetchM___redArg___closed__18;
lean_ctor_set_tag(x_192, 1);
lean_ctor_set(x_192, 0, x_200);
return x_192;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_dec(x_192);
x_202 = l_Lake_Workspace_runFetchM___redArg___closed__18;
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
block_220:
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_array_get_size(x_206);
x_212 = lean_nat_dec_lt(x_42, x_211);
if (x_212 == 0)
{
lean_dec(x_211);
lean_dec_ref(x_206);
lean_dec(x_31);
x_166 = x_205;
x_167 = x_207;
x_168 = x_209;
x_169 = x_208;
x_170 = x_210;
goto block_204;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_211, x_211);
if (x_213 == 0)
{
lean_dec(x_211);
lean_dec_ref(x_206);
lean_dec(x_31);
x_166 = x_205;
x_167 = x_207;
x_168 = x_209;
x_169 = x_208;
x_170 = x_210;
goto block_204;
}
else
{
lean_object* x_214; size_t x_215; size_t x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_box(0);
x_215 = 0;
x_216 = lean_usize_of_nat(x_211);
lean_dec(x_211);
x_217 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_22);
x_218 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(x_22, x_12, x_217, x_206, x_215, x_216, x_214, x_210);
lean_dec_ref(x_206);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec_ref(x_218);
x_166 = x_205;
x_167 = x_207;
x_168 = x_209;
x_169 = x_208;
x_170 = x_219;
goto block_204;
}
}
}
block_241:
{
if (x_225 == 0)
{
lean_dec_ref(x_230);
lean_dec(x_31);
x_166 = x_226;
x_167 = x_227;
x_168 = x_229;
x_169 = x_228;
x_170 = x_231;
goto block_204;
}
else
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_array_get_size(x_230);
x_233 = lean_nat_dec_lt(x_42, x_232);
if (x_233 == 0)
{
lean_dec(x_232);
lean_dec_ref(x_230);
lean_dec(x_31);
x_166 = x_226;
x_167 = x_227;
x_168 = x_229;
x_169 = x_228;
x_170 = x_231;
goto block_204;
}
else
{
uint8_t x_234; 
x_234 = lean_nat_dec_le(x_232, x_232);
if (x_234 == 0)
{
lean_dec(x_232);
lean_dec_ref(x_230);
lean_dec(x_31);
x_166 = x_226;
x_167 = x_227;
x_168 = x_229;
x_169 = x_228;
x_170 = x_231;
goto block_204;
}
else
{
lean_object* x_235; size_t x_236; size_t x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; 
x_235 = lean_box(0);
x_236 = 0;
x_237 = lean_usize_of_nat(x_232);
lean_dec(x_232);
x_238 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_22);
x_239 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(x_22, x_12, x_238, x_230, x_236, x_237, x_235, x_231);
lean_dec_ref(x_230);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec_ref(x_239);
x_166 = x_226;
x_167 = x_227;
x_168 = x_229;
x_169 = x_228;
x_170 = x_240;
goto block_204;
}
}
}
}
block_311:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_244 = lean_ctor_get(x_34, 3);
lean_inc(x_244);
lean_dec(x_34);
x_245 = l_Lake_Job_toOpaque___redArg(x_223);
x_246 = lean_unsigned_to_nat(1u);
x_247 = l_Lake_Workspace_runFetchM___redArg___closed__20;
x_248 = lean_array_push(x_247, x_245);
x_249 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
x_250 = lean_unsigned_to_nat(100u);
x_251 = lean_unbox(x_31);
lean_inc(x_22);
x_252 = l_Lake_monitorJobs(x_248, x_244, x_22, x_11, x_12, x_242, x_225, x_251, x_165, x_243, x_249, x_154, x_250, x_163);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec_ref(x_252);
x_255 = lean_ctor_get_uint8(x_253, sizeof(void*)*2);
x_256 = lean_ctor_get(x_253, 0);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
lean_dec(x_253);
x_258 = l_Lake_Workspace_saveInputs(x_1, x_154, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec_ref(x_258);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec_ref(x_259);
x_262 = lean_array_get_size(x_261);
x_263 = lean_nat_dec_eq(x_262, x_42);
lean_dec(x_262);
if (x_263 == 0)
{
if (x_225 == 0)
{
lean_dec(x_261);
lean_dec(x_31);
x_166 = x_246;
x_167 = x_257;
x_168 = x_256;
x_169 = x_255;
x_170 = x_260;
goto block_204;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_22, 4);
x_265 = l_Lake_Workspace_runFetchM___redArg___closed__21;
lean_inc_ref(x_264);
x_266 = lean_apply_2(x_264, x_265, x_260);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec_ref(x_266);
x_205 = x_246;
x_206 = x_261;
x_207 = x_257;
x_208 = x_255;
x_209 = x_256;
x_210 = x_267;
goto block_220;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec_ref(x_266);
x_270 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_271 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_272 = lean_unsigned_to_nat(84u);
x_273 = lean_unsigned_to_nat(4u);
x_274 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__4;
x_275 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
x_276 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_275, x_225);
x_277 = lean_string_append(x_274, x_276);
lean_dec_ref(x_276);
x_278 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
x_279 = lean_string_append(x_277, x_278);
x_280 = lean_io_error_to_string(x_268);
x_281 = lean_string_append(x_279, x_280);
lean_dec_ref(x_280);
x_282 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_283 = lean_string_append(x_281, x_282);
x_284 = l_Lake_Workspace_runFetchM___redArg___closed__24;
x_285 = lean_string_append(x_283, x_284);
x_286 = l_mkPanicMessageWithDecl(x_270, x_271, x_272, x_273, x_285);
lean_dec_ref(x_285);
x_287 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_286, x_269);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec_ref(x_287);
x_205 = x_246;
x_206 = x_261;
x_207 = x_257;
x_208 = x_255;
x_209 = x_256;
x_210 = x_288;
goto block_220;
}
}
}
else
{
lean_dec(x_261);
lean_dec(x_31);
x_166 = x_246;
x_167 = x_257;
x_168 = x_256;
x_169 = x_255;
x_170 = x_260;
goto block_204;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_258, 1);
lean_inc(x_289);
lean_dec_ref(x_258);
x_290 = lean_ctor_get(x_259, 1);
lean_inc(x_290);
lean_dec_ref(x_259);
x_291 = lean_ctor_get(x_22, 4);
x_292 = l_Lake_Workspace_runFetchM___redArg___closed__25;
lean_inc_ref(x_291);
x_293 = lean_apply_2(x_291, x_292, x_289);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec_ref(x_293);
x_226 = x_246;
x_227 = x_257;
x_228 = x_255;
x_229 = x_256;
x_230 = x_290;
x_231 = x_294;
goto block_241;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec_ref(x_293);
x_297 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
x_298 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
x_299 = lean_unsigned_to_nat(84u);
x_300 = lean_unsigned_to_nat(4u);
x_301 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_302 = lean_io_error_to_string(x_295);
x_303 = lean_string_append(x_301, x_302);
lean_dec_ref(x_302);
x_304 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__21;
x_305 = lean_string_append(x_303, x_304);
x_306 = l_Lake_Workspace_runFetchM___redArg___closed__28;
x_307 = lean_string_append(x_305, x_306);
x_308 = l_mkPanicMessageWithDecl(x_297, x_298, x_299, x_300, x_307);
lean_dec_ref(x_307);
x_309 = l_panic___at_____private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_308, x_296);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec_ref(x_309);
x_226 = x_246;
x_227 = x_257;
x_228 = x_255;
x_229 = x_256;
x_230 = x_290;
x_231 = x_310;
goto block_241;
}
}
}
block_314:
{
if (x_225 == 0)
{
uint8_t x_313; 
x_313 = lean_unbox(x_31);
if (x_313 == 0)
{
x_242 = x_312;
x_243 = x_153;
goto block_311;
}
else
{
x_242 = x_312;
x_243 = x_225;
goto block_311;
}
}
else
{
x_242 = x_312;
x_243 = x_225;
goto block_311;
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
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
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__9(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_Workspace_runFetchM___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Index(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin, lean_io_mk_world());
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
l_Lake_Workspace_runFetchM___redArg___closed__0 = _init_l_Lake_Workspace_runFetchM___redArg___closed__0();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__0);
l_Lake_Workspace_runFetchM___redArg___closed__1 = _init_l_Lake_Workspace_runFetchM___redArg___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__1);
l_Lake_Workspace_runFetchM___redArg___closed__2 = _init_l_Lake_Workspace_runFetchM___redArg___closed__2();
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
l_Lake_Workspace_runFetchM___redArg___closed__26 = _init_l_Lake_Workspace_runFetchM___redArg___closed__26();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__26);
l_Lake_Workspace_runFetchM___redArg___closed__27 = _init_l_Lake_Workspace_runFetchM___redArg___closed__27();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__27);
l_Lake_Workspace_runFetchM___redArg___closed__28 = _init_l_Lake_Workspace_runFetchM___redArg___closed__28();
lean_mark_persistent(l_Lake_Workspace_runFetchM___redArg___closed__28);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
