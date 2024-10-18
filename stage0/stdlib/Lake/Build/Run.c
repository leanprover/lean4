// Lean compiler output
// Module: Lake.Build.Run
// Imports: Init Lake.Util.Lock Lake.Build.Index
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
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__5;
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_print_x21___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_MonitorM_run(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__3;
extern lean_object* l_Lake_instOrdLogLevel;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__9;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__5;
static lean_object* l_Lake_print_x21___closed__10;
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__2;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__3;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__4;
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__8(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__5;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lake_print_x21(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instOrdJobAction;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__3;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__7(lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__5;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__6;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__5;
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__6;
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__7;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__2;
static lean_object* l_Lake_Monitor_renderProgress___closed__2;
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lake_print_x21___closed__8;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__1;
static lean_object* l_Lake_print_x21___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__2(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames;
lean_object* l_Lake_recFetch___at_Lake_FetchM_run___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__3;
static uint8_t l_Lake_Monitor_reportJob___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_print_x21___closed__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lake_print_x21___spec__1(lean_object*, lean_object*);
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__4;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__3;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__6;
extern lean_object* l_Std_Format_defWidth;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lake_print_x21___closed__5;
static lean_object* l_Lake_mkBuildContext___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Ansi_resetLine___closed__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1;
static lean_object* l_Lake_Monitor_sleep___closed__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__5;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__8;
static lean_object* l_Lake_Monitor_renderProgress___closed__1;
static lean_object* l_Lake_Monitor_poll___closed__1;
LEAN_EXPORT lean_object* l_Lake_Ansi_resetLine;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__5(lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__11;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__12;
static lean_object* l_Lake_print_x21___closed__13;
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_EquipT_bind___at_Lake_LeanExe_recBuildExe___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_poll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__11;
static lean_object* l_Lake_print_x21___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_panic___at_Lake_print_x21___spec__1___closed__1;
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__3;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
static uint8_t l_Lake_Monitor_reportJob___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__9;
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_runBuild___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__2;
LEAN_EXPORT lean_object* l_Lake_flush(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__7;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_print_x21___lambda__1(lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__6;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__3;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__4;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lake_mkBuildContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_mkBuildContext___closed__2;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_mkBuildContext___closed__1;
x_5 = lean_st_mk_ref(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lake_Env_leanGithash(x_8);
lean_dec(x_8);
x_10 = lean_string_hash(x_9);
lean_dec(x_9);
x_11 = 1723;
x_12 = lean_uint64_mix_hash(x_11, x_10);
x_13 = l_Lake_mkBuildContext___closed__3;
x_14 = lean_box_uint64(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_7);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = l_Lake_Env_leanGithash(x_19);
lean_dec(x_19);
x_21 = lean_string_hash(x_20);
lean_dec(x_20);
x_22 = 1723;
x_23 = lean_uint64_mix_hash(x_22, x_21);
x_24 = l_Lake_mkBuildContext___closed__3;
x_25 = lean_box_uint64(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10493;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10491;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10431;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10367;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10463;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10479;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10487;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10494;
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
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__8;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Monitor_spinnerFrames___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_3, x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_MonitorM_run___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_Ansi_resetLine___closed__1() {
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
x_1 = l_Lake_Ansi_resetLine___closed__1;
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
static lean_object* _init_l_panic___at_Lake_print_x21___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadBaseIO;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lake_print_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_panic___at_Lake_print_x21___spec__1___closed__1;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lake_print_x21___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_print_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("print!", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_print_x21___closed__1;
x_2 = l_Lake_print_x21___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_print_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_print_x21___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_print_x21___closed__3;
x_2 = 1;
x_3 = l_Lake_print_x21___closed__4;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_print_x21___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_print_x21___closed__6;
x_2 = l_Lake_print_x21___closed__5;
x_3 = lean_string_append(x_1, x_2);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_print_x21___closed__7;
x_2 = l_Lake_print_x21___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_print_x21___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_print_x21___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.print!", 11, 11);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_io_error_to_string(x_10);
x_13 = l_Lake_print_x21___closed__9;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_print_x21___closed__10;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_String_quote(x_2);
lean_dec(x_2);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Std_Format_defWidth;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_format_pretty(x_18, x_19, x_20, x_20);
x_22 = lean_string_append(x_16, x_21);
lean_dec(x_21);
x_23 = l_Lake_print_x21___closed__11;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lake_print_x21___closed__12;
x_26 = l_Lake_print_x21___closed__13;
x_27 = lean_unsigned_to_nat(75u);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_24);
lean_dec(x_24);
x_30 = l_panic___at_Lake_print_x21___spec__1(x_29, x_11);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_print_x21___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_print_x21___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = lean_apply_2(x_6, x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
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
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_io_error_to_string(x_15);
x_18 = l_Lake_print_x21___closed__9;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lake_print_x21___closed__10;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_String_quote(x_1);
lean_dec(x_1);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Std_Format_defWidth;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_format_pretty(x_23, x_24, x_25, x_25);
x_27 = lean_string_append(x_21, x_26);
lean_dec(x_26);
x_28 = l_Lake_print_x21___closed__11;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lake_print_x21___closed__12;
x_31 = l_Lake_print_x21___closed__13;
x_32 = lean_unsigned_to_nat(75u);
x_33 = lean_unsigned_to_nat(4u);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_29);
lean_dec(x_29);
x_35 = l_panic___at_Lake_print_x21___spec__1(x_34, x_16);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Monitor_spinnerFrames;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" [", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Running ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (+ ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_renderProgress___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" more)", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lake_Monitor_spinnerFrames;
x_22 = lean_array_fget(x_21, x_18);
x_23 = lean_unbox_uint32(x_22);
lean_dec(x_22);
x_24 = l_Lake_Monitor_renderProgress___closed__1;
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Fin_add(x_24, x_18, x_25);
lean_dec(x_18);
x_27 = l_Lake_Ansi_resetLine;
lean_inc(x_16);
lean_ctor_set(x_5, 4, x_26);
lean_ctor_set(x_5, 2, x_27);
x_28 = lean_array_get_size(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
x_31 = l_Lake_print_x21___closed__11;
x_32 = lean_string_append(x_31, x_17);
lean_dec(x_17);
x_33 = lean_string_append(x_32, x_31);
x_34 = lean_string_push(x_31, x_23);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Lake_Monitor_renderProgress___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lake_Monitor_renderProgress___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = l_Lake_print_x21___closed__10;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_ctor_get(x_20, 4);
lean_inc(x_46);
if (x_30 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_28);
x_153 = lean_array_fget(x_2, x_29);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l_Lake_Monitor_renderProgress___closed__4;
x_156 = lean_string_append(x_155, x_154);
lean_dec(x_154);
x_157 = lean_string_append(x_156, x_31);
x_47 = x_157;
goto block_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_158 = lean_array_fget(x_1, x_29);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = l_Lake_Monitor_renderProgress___closed__4;
x_161 = lean_string_append(x_160, x_159);
lean_dec(x_159);
x_162 = l_Lake_Monitor_renderProgress___closed__5;
x_163 = lean_string_append(x_161, x_162);
x_164 = lean_nat_sub(x_28, x_25);
lean_dec(x_28);
x_165 = l___private_Init_Data_Repr_0__Nat_reprFast(x_164);
x_166 = lean_string_append(x_163, x_165);
lean_dec(x_165);
x_167 = l_Lake_Monitor_renderProgress___closed__6;
x_168 = lean_string_append(x_166, x_167);
x_47 = x_168;
goto block_152;
}
block_152:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_string_append(x_45, x_47);
lean_dec(x_47);
x_49 = lean_string_append(x_48, x_31);
lean_inc(x_49);
x_50 = lean_apply_2(x_46, x_49, x_6);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_apply_1(x_54, x_52);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_57);
lean_ctor_set(x_55, 0, x_50);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_63);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 0, x_50);
return x_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_dec(x_55);
x_65 = lean_box(0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_50);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_ctor_get(x_20, 0);
lean_inc(x_68);
lean_dec(x_20);
x_69 = lean_apply_1(x_68, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_5);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_5);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_50);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_81 = lean_ctor_get(x_50, 0);
x_82 = lean_ctor_get(x_50, 1);
x_83 = lean_io_error_to_string(x_81);
x_84 = l_Lake_print_x21___closed__9;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = lean_string_append(x_85, x_44);
x_87 = l_String_quote(x_49);
lean_dec(x_49);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Std_Format_defWidth;
x_90 = lean_format_pretty(x_88, x_89, x_29, x_29);
x_91 = lean_string_append(x_86, x_90);
lean_dec(x_90);
x_92 = lean_string_append(x_91, x_31);
x_93 = l_Lake_print_x21___closed__12;
x_94 = l_Lake_print_x21___closed__13;
x_95 = lean_unsigned_to_nat(75u);
x_96 = lean_unsigned_to_nat(4u);
x_97 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_93, x_94, x_95, x_96, x_92);
lean_dec(x_92);
x_98 = l_panic___at_Lake_print_x21___spec__1(x_97, x_82);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_20, 0);
lean_inc(x_100);
lean_dec(x_20);
x_101 = lean_apply_1(x_100, x_99);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 0);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_103);
lean_ctor_set(x_101, 0, x_50);
return x_101;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_101);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_50);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_101);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_101, 0);
lean_dec(x_108);
x_109 = lean_box(0);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_109);
lean_ctor_set_tag(x_101, 0);
lean_ctor_set(x_101, 0, x_50);
return x_101;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
x_111 = lean_box(0);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 0, x_111);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_50);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_free_object(x_50);
lean_dec(x_5);
lean_dec(x_20);
x_113 = !lean_is_exclusive(x_98);
if (x_113 == 0)
{
return x_98;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_98, 0);
x_115 = lean_ctor_get(x_98, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_98);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_117 = lean_ctor_get(x_50, 0);
x_118 = lean_ctor_get(x_50, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_50);
x_119 = lean_io_error_to_string(x_117);
x_120 = l_Lake_print_x21___closed__9;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
x_122 = lean_string_append(x_121, x_44);
x_123 = l_String_quote(x_49);
lean_dec(x_49);
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Std_Format_defWidth;
x_126 = lean_format_pretty(x_124, x_125, x_29, x_29);
x_127 = lean_string_append(x_122, x_126);
lean_dec(x_126);
x_128 = lean_string_append(x_127, x_31);
x_129 = l_Lake_print_x21___closed__12;
x_130 = l_Lake_print_x21___closed__13;
x_131 = lean_unsigned_to_nat(75u);
x_132 = lean_unsigned_to_nat(4u);
x_133 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_129, x_130, x_131, x_132, x_128);
lean_dec(x_128);
x_134 = l_panic___at_Lake_print_x21___spec__1(x_133, x_118);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_ctor_get(x_20, 0);
lean_inc(x_136);
lean_dec(x_20);
x_137 = lean_apply_1(x_136, x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_5);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
 x_144 = lean_box(0);
}
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_5);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_144;
 lean_ctor_set_tag(x_147, 0);
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_5);
lean_dec(x_20);
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint32_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_169 = lean_ctor_get(x_5, 0);
x_170 = lean_ctor_get(x_5, 1);
x_171 = lean_ctor_get(x_5, 2);
x_172 = lean_ctor_get(x_5, 3);
x_173 = lean_ctor_get(x_5, 4);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_5);
x_174 = lean_ctor_get(x_4, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_4, 1);
lean_inc(x_175);
lean_dec(x_4);
x_176 = l_Lake_Monitor_spinnerFrames;
x_177 = lean_array_fget(x_176, x_173);
x_178 = lean_unbox_uint32(x_177);
lean_dec(x_177);
x_179 = l_Lake_Monitor_renderProgress___closed__1;
x_180 = lean_unsigned_to_nat(1u);
x_181 = l_Fin_add(x_179, x_173, x_180);
lean_dec(x_173);
x_182 = l_Lake_Ansi_resetLine;
lean_inc(x_169);
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_170);
lean_ctor_set(x_183, 2, x_182);
lean_ctor_set(x_183, 3, x_172);
lean_ctor_set(x_183, 4, x_181);
x_184 = lean_array_get_size(x_1);
x_185 = lean_unsigned_to_nat(0u);
x_186 = lean_nat_dec_lt(x_185, x_184);
x_187 = l_Lake_print_x21___closed__11;
x_188 = lean_string_append(x_187, x_171);
lean_dec(x_171);
x_189 = lean_string_append(x_188, x_187);
x_190 = lean_string_push(x_187, x_178);
x_191 = lean_string_append(x_189, x_190);
lean_dec(x_190);
x_192 = l_Lake_Monitor_renderProgress___closed__2;
x_193 = lean_string_append(x_191, x_192);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_169);
x_195 = lean_string_append(x_193, x_194);
lean_dec(x_194);
x_196 = l_Lake_Monitor_renderProgress___closed__3;
x_197 = lean_string_append(x_195, x_196);
x_198 = l___private_Init_Data_Repr_0__Nat_reprFast(x_174);
x_199 = lean_string_append(x_197, x_198);
lean_dec(x_198);
x_200 = l_Lake_print_x21___closed__10;
x_201 = lean_string_append(x_199, x_200);
x_202 = lean_ctor_get(x_175, 4);
lean_inc(x_202);
if (x_186 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_184);
x_258 = lean_array_fget(x_2, x_185);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_260 = l_Lake_Monitor_renderProgress___closed__4;
x_261 = lean_string_append(x_260, x_259);
lean_dec(x_259);
x_262 = lean_string_append(x_261, x_187);
x_203 = x_262;
goto block_257;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_263 = lean_array_fget(x_1, x_185);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = l_Lake_Monitor_renderProgress___closed__4;
x_266 = lean_string_append(x_265, x_264);
lean_dec(x_264);
x_267 = l_Lake_Monitor_renderProgress___closed__5;
x_268 = lean_string_append(x_266, x_267);
x_269 = lean_nat_sub(x_184, x_180);
lean_dec(x_184);
x_270 = l___private_Init_Data_Repr_0__Nat_reprFast(x_269);
x_271 = lean_string_append(x_268, x_270);
lean_dec(x_270);
x_272 = l_Lake_Monitor_renderProgress___closed__6;
x_273 = lean_string_append(x_271, x_272);
x_203 = x_273;
goto block_257;
}
block_257:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_string_append(x_201, x_203);
lean_dec(x_203);
x_205 = lean_string_append(x_204, x_187);
lean_inc(x_205);
x_206 = lean_apply_2(x_202, x_205, x_6);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_205);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_175, 0);
lean_inc(x_209);
lean_dec(x_175);
x_210 = lean_apply_1(x_209, x_207);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_208;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_183);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_217 = x_210;
} else {
 lean_dec_ref(x_210);
 x_217 = lean_box(0);
}
x_218 = lean_box(0);
if (lean_is_scalar(x_208)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_208;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_183);
if (lean_is_scalar(x_217)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_217;
 lean_ctor_set_tag(x_220, 0);
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_221 = lean_ctor_get(x_206, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_206, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_223 = x_206;
} else {
 lean_dec_ref(x_206);
 x_223 = lean_box(0);
}
x_224 = lean_io_error_to_string(x_221);
x_225 = l_Lake_print_x21___closed__9;
x_226 = lean_string_append(x_225, x_224);
lean_dec(x_224);
x_227 = lean_string_append(x_226, x_200);
x_228 = l_String_quote(x_205);
lean_dec(x_205);
x_229 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = l_Std_Format_defWidth;
x_231 = lean_format_pretty(x_229, x_230, x_185, x_185);
x_232 = lean_string_append(x_227, x_231);
lean_dec(x_231);
x_233 = lean_string_append(x_232, x_187);
x_234 = l_Lake_print_x21___closed__12;
x_235 = l_Lake_print_x21___closed__13;
x_236 = lean_unsigned_to_nat(75u);
x_237 = lean_unsigned_to_nat(4u);
x_238 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_234, x_235, x_236, x_237, x_233);
lean_dec(x_233);
x_239 = l_panic___at_Lake_print_x21___spec__1(x_238, x_222);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = lean_ctor_get(x_175, 0);
lean_inc(x_241);
lean_dec(x_175);
x_242 = lean_apply_1(x_241, x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_223;
 lean_ctor_set_tag(x_246, 0);
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_183);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_223;
 lean_ctor_set_tag(x_251, 0);
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_183);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
 lean_ctor_set_tag(x_252, 0);
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_223);
lean_dec(x_183);
lean_dec(x_175);
x_253 = lean_ctor_get(x_239, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_239, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_255 = x_239;
} else {
 lean_dec_ref(x_239);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_5, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_7);
x_12 = lean_array_uget(x_4, x_5);
lean_inc(x_1);
x_13 = l_Lake_logToStream(x_12, x_1, x_2, x_3, x_10);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_7 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_4, x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_6);
x_11 = lean_array_uget(x_3, x_4);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lake_logToStream(x_11, x_1, x_12, x_2, x_9);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_6 = x_14;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
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
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Monitor_reportJob___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("32", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_Monitor_reportJob___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (Optional)", 11, 11);
return x_1;
}
}
static uint8_t _init_l_Lake_Monitor_reportJob___lambda__2___closed__7() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_Monitor_reportJob___lambda__2___closed__8() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, uint8_t x_11, uint8_t x_12, uint8_t x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
if (x_14 == 0)
{
uint8_t x_331; 
x_331 = 0;
x_19 = x_331;
goto block_330;
}
else
{
uint8_t x_332; 
x_332 = 1;
x_19 = x_332;
goto block_330;
}
block_330:
{
lean_object* x_20; lean_object* x_278; lean_object* x_307; uint8_t x_324; 
x_324 = l_instDecidableNot___rarg(x_19);
if (x_324 == 0)
{
if (x_13 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_325 = lean_box(0);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_17);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_18);
return x_327;
}
else
{
lean_object* x_328; 
x_328 = lean_box(0);
x_307 = x_328;
goto block_323;
}
}
else
{
lean_object* x_329; 
x_329 = lean_box(0);
x_307 = x_329;
goto block_323;
}
block_277:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
x_21 = lean_array_get_size(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
x_24 = l_instDecidableNot___rarg(x_23);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
if (x_24 == 0)
{
uint8_t x_275; 
x_275 = 0;
x_27 = x_275;
goto block_274;
}
else
{
uint8_t x_276; 
x_276 = 1;
x_27 = x_276;
goto block_274;
}
block_274:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_267; 
x_267 = 0;
x_28 = x_267;
goto block_266;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_268 = l_Lake_instOrdLogLevel;
x_269 = lean_box(x_10);
x_270 = lean_box(x_9);
x_271 = l_instDecidableRelLe___rarg(x_268, x_269, x_270);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = 0;
x_28 = x_272;
goto block_266;
}
else
{
uint8_t x_273; 
x_273 = 1;
x_28 = x_273;
goto block_266;
}
}
block_266:
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lake_JobAction_verb(x_28, x_4);
if (x_28 == 0)
{
if (x_27 == 0)
{
uint8_t x_258; 
x_258 = 0;
x_30 = x_258;
goto block_257;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_259 = l_Lake_instOrdLogLevel;
x_260 = lean_box(x_6);
x_261 = lean_box(x_9);
x_262 = l_instDecidableRelLe___rarg(x_259, x_260, x_261);
if (x_262 == 0)
{
uint8_t x_263; 
x_263 = 0;
x_30 = x_263;
goto block_257;
}
else
{
uint8_t x_264; 
x_264 = 1;
x_30 = x_264;
goto block_257;
}
}
}
else
{
uint8_t x_265; 
x_265 = 1;
x_30 = x_265;
goto block_257;
}
block_257:
{
lean_object* x_31; uint32_t x_219; 
if (x_30 == 0)
{
uint32_t x_255; 
x_255 = 10004;
x_219 = x_255;
goto block_254;
}
else
{
uint32_t x_256; 
x_256 = l_Lake_LogLevel_icon(x_9);
x_219 = x_256;
goto block_254;
}
block_218:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_33 = lean_ctor_get(x_17, 2);
x_34 = l_Lake_print_x21___closed__11;
lean_ctor_set(x_17, 2, x_34);
x_71 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_72 = lean_string_append(x_71, x_34);
x_73 = lean_string_append(x_72, x_31);
lean_dec(x_31);
x_74 = l_Lake_Monitor_reportJob___lambda__2___closed__2;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_ctor_get(x_16, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 4);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_75);
x_78 = lean_apply_2(x_77, x_75, x_18);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
lean_dec(x_75);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 1);
lean_ctor_set(x_78, 1, x_17);
x_35 = x_78;
x_36 = x_80;
goto block_70;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_78);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_17);
x_35 = x_83;
x_36 = x_82;
goto block_70;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_78);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_85 = lean_ctor_get(x_78, 0);
x_86 = lean_ctor_get(x_78, 1);
x_87 = lean_io_error_to_string(x_85);
x_88 = l_Lake_print_x21___closed__9;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = l_Lake_print_x21___closed__10;
x_91 = lean_string_append(x_89, x_90);
x_92 = l_String_quote(x_75);
lean_dec(x_75);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Std_Format_defWidth;
x_95 = lean_format_pretty(x_93, x_94, x_22, x_22);
x_96 = lean_string_append(x_91, x_95);
lean_dec(x_95);
x_97 = lean_string_append(x_96, x_34);
x_98 = l_Lake_print_x21___closed__12;
x_99 = l_Lake_print_x21___closed__13;
x_100 = lean_unsigned_to_nat(75u);
x_101 = lean_unsigned_to_nat(4u);
x_102 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_98, x_99, x_100, x_101, x_97);
lean_dec(x_97);
x_103 = l_panic___at_Lake_print_x21___spec__1(x_102, x_86);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_ctor_set_tag(x_78, 0);
lean_ctor_set(x_78, 1, x_17);
lean_ctor_set(x_78, 0, x_104);
x_35 = x_78;
x_36 = x_105;
goto block_70;
}
else
{
uint8_t x_106; 
lean_free_object(x_78);
lean_dec(x_17);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_5);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_110 = lean_ctor_get(x_78, 0);
x_111 = lean_ctor_get(x_78, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_78);
x_112 = lean_io_error_to_string(x_110);
x_113 = l_Lake_print_x21___closed__9;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lake_print_x21___closed__10;
x_116 = lean_string_append(x_114, x_115);
x_117 = l_String_quote(x_75);
lean_dec(x_75);
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Std_Format_defWidth;
x_120 = lean_format_pretty(x_118, x_119, x_22, x_22);
x_121 = lean_string_append(x_116, x_120);
lean_dec(x_120);
x_122 = lean_string_append(x_121, x_34);
x_123 = l_Lake_print_x21___closed__12;
x_124 = l_Lake_print_x21___closed__13;
x_125 = lean_unsigned_to_nat(75u);
x_126 = lean_unsigned_to_nat(4u);
x_127 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_123, x_124, x_125, x_126, x_122);
lean_dec(x_122);
x_128 = l_panic___at_Lake_print_x21___spec__1(x_127, x_111);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_17);
x_35 = x_131;
x_36 = x_130;
goto block_70;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_17);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_5);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
block_70:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lake_Monitor_reportJob___lambda__2___closed__1;
if (x_30 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_21);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_apply_4(x_38, x_39, x_16, x_37, x_36);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_lt(x_22, x_21);
if (x_28 == 0)
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_21);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = lean_apply_4(x_38, x_42, x_16, x_37, x_36);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_21, x_21);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_21);
lean_dec(x_5);
x_45 = lean_box(0);
x_46 = lean_apply_4(x_38, x_45, x_16, x_37, x_36);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(x_5, x_6, x_7, x_1, x_47, x_48, x_49, x_16, x_37, x_36);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_apply_4(x_38, x_53, x_16, x_54, x_52);
return x_55;
}
}
}
else
{
if (x_41 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_21);
lean_dec(x_5);
x_56 = lean_box(0);
x_57 = lean_apply_4(x_38, x_56, x_16, x_37, x_36);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_21, x_21);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_21);
lean_dec(x_5);
x_59 = lean_box(0);
x_60 = lean_apply_4(x_38, x_59, x_16, x_37, x_36);
return x_60;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_63 = lean_box(0);
x_64 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(x_5, x_7, x_1, x_61, x_62, x_63, x_16, x_37, x_36);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_apply_4(x_38, x_67, x_16, x_68, x_66);
return x_69;
}
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_136 = lean_ctor_get(x_17, 0);
x_137 = lean_ctor_get(x_17, 1);
x_138 = lean_ctor_get(x_17, 2);
x_139 = lean_ctor_get(x_17, 3);
x_140 = lean_ctor_get(x_17, 4);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_17);
x_141 = l_Lake_print_x21___closed__11;
x_142 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_137);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_142, 3, x_139);
lean_ctor_set(x_142, 4, x_140);
x_179 = lean_string_append(x_141, x_138);
lean_dec(x_138);
x_180 = lean_string_append(x_179, x_141);
x_181 = lean_string_append(x_180, x_31);
lean_dec(x_31);
x_182 = l_Lake_Monitor_reportJob___lambda__2___closed__2;
x_183 = lean_string_append(x_181, x_182);
x_184 = lean_ctor_get(x_16, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 4);
lean_inc(x_185);
lean_dec(x_184);
lean_inc(x_183);
x_186 = lean_apply_2(x_185, x_183, x_18);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_183);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_142);
x_143 = x_190;
x_144 = x_188;
goto block_178;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_191 = lean_ctor_get(x_186, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_193 = x_186;
} else {
 lean_dec_ref(x_186);
 x_193 = lean_box(0);
}
x_194 = lean_io_error_to_string(x_191);
x_195 = l_Lake_print_x21___closed__9;
x_196 = lean_string_append(x_195, x_194);
lean_dec(x_194);
x_197 = l_Lake_print_x21___closed__10;
x_198 = lean_string_append(x_196, x_197);
x_199 = l_String_quote(x_183);
lean_dec(x_183);
x_200 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Std_Format_defWidth;
x_202 = lean_format_pretty(x_200, x_201, x_22, x_22);
x_203 = lean_string_append(x_198, x_202);
lean_dec(x_202);
x_204 = lean_string_append(x_203, x_141);
x_205 = l_Lake_print_x21___closed__12;
x_206 = l_Lake_print_x21___closed__13;
x_207 = lean_unsigned_to_nat(75u);
x_208 = lean_unsigned_to_nat(4u);
x_209 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_205, x_206, x_207, x_208, x_204);
lean_dec(x_204);
x_210 = l_panic___at_Lake_print_x21___spec__1(x_209, x_192);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
if (lean_is_scalar(x_193)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_193;
 lean_ctor_set_tag(x_213, 0);
}
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_142);
x_143 = x_213;
x_144 = x_212;
goto block_178;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_193);
lean_dec(x_142);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_5);
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_216 = x_210;
} else {
 lean_dec_ref(x_210);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
block_178:
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lake_Monitor_reportJob___lambda__2___closed__1;
if (x_30 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_21);
lean_dec(x_5);
x_147 = lean_box(0);
x_148 = lean_apply_4(x_146, x_147, x_16, x_145, x_144);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = lean_nat_dec_lt(x_22, x_21);
if (x_28 == 0)
{
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_21);
lean_dec(x_5);
x_150 = lean_box(0);
x_151 = lean_apply_4(x_146, x_150, x_16, x_145, x_144);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_21, x_21);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_21);
lean_dec(x_5);
x_153 = lean_box(0);
x_154 = lean_apply_4(x_146, x_153, x_16, x_145, x_144);
return x_154;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = 0;
x_156 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_157 = lean_box(0);
x_158 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(x_5, x_6, x_7, x_1, x_155, x_156, x_157, x_16, x_145, x_144);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_apply_4(x_146, x_161, x_16, x_162, x_160);
return x_163;
}
}
}
else
{
if (x_149 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_21);
lean_dec(x_5);
x_164 = lean_box(0);
x_165 = lean_apply_4(x_146, x_164, x_16, x_145, x_144);
return x_165;
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_le(x_21, x_21);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_21);
lean_dec(x_5);
x_167 = lean_box(0);
x_168 = lean_apply_4(x_146, x_167, x_16, x_145, x_144);
return x_168;
}
else
{
size_t x_169; size_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_169 = 0;
x_170 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_171 = lean_box(0);
x_172 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(x_5, x_7, x_1, x_169, x_170, x_171, x_16, x_145, x_144);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_apply_4(x_146, x_175, x_16, x_176, x_174);
return x_177;
}
}
}
}
}
}
}
block_254:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_220 = l_Lake_print_x21___closed__11;
x_221 = lean_string_push(x_220, x_219);
x_222 = lean_string_append(x_220, x_221);
lean_dec(x_221);
x_223 = l_Lake_Monitor_renderProgress___closed__2;
x_224 = lean_string_append(x_222, x_223);
x_225 = lean_string_append(x_224, x_25);
lean_dec(x_25);
x_226 = l_Lake_Monitor_renderProgress___closed__3;
x_227 = lean_string_append(x_225, x_226);
x_228 = lean_string_append(x_227, x_26);
lean_dec(x_26);
x_229 = l_Lake_Monitor_reportJob___lambda__2___closed__3;
x_230 = lean_string_append(x_228, x_229);
if (x_19 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_string_append(x_230, x_220);
x_232 = l_Lake_Monitor_reportJob___lambda__2___closed__4;
x_233 = lean_string_append(x_231, x_232);
x_234 = lean_string_append(x_233, x_29);
lean_dec(x_29);
x_235 = lean_string_append(x_234, x_232);
x_236 = lean_string_append(x_235, x_8);
x_237 = lean_string_append(x_236, x_220);
if (x_7 == 0)
{
x_31 = x_237;
goto block_218;
}
else
{
if (x_30 == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = l_Lake_Monitor_reportJob___lambda__2___closed__5;
x_239 = l_Lake_Ansi_chalk(x_238, x_237);
lean_dec(x_237);
x_31 = x_239;
goto block_218;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = l_Lake_LogLevel_ansiColor(x_9);
x_241 = l_Lake_Ansi_chalk(x_240, x_237);
lean_dec(x_237);
lean_dec(x_240);
x_31 = x_241;
goto block_218;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_242 = l_Lake_Monitor_reportJob___lambda__2___closed__6;
x_243 = lean_string_append(x_230, x_242);
x_244 = l_Lake_Monitor_reportJob___lambda__2___closed__4;
x_245 = lean_string_append(x_243, x_244);
x_246 = lean_string_append(x_245, x_29);
lean_dec(x_29);
x_247 = lean_string_append(x_246, x_244);
x_248 = lean_string_append(x_247, x_8);
x_249 = lean_string_append(x_248, x_220);
if (x_7 == 0)
{
x_31 = x_249;
goto block_218;
}
else
{
if (x_30 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_Lake_Monitor_reportJob___lambda__2___closed__5;
x_251 = l_Lake_Ansi_chalk(x_250, x_249);
lean_dec(x_249);
x_31 = x_251;
goto block_218;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Lake_LogLevel_ansiColor(x_9);
x_253 = l_Lake_Ansi_chalk(x_252, x_249);
lean_dec(x_249);
lean_dec(x_252);
x_31 = x_253;
goto block_218;
}
}
}
}
}
}
}
}
block_306:
{
lean_dec(x_278);
if (x_11 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_279 = lean_box(0);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_17);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_18);
return x_281;
}
else
{
if (x_7 == 0)
{
uint8_t x_282; 
x_282 = l_Lake_Monitor_reportJob___lambda__2___closed__7;
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_17);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_18);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_286 = l_Lake_instOrdJobAction;
x_287 = lean_box(x_12);
x_288 = lean_box(x_4);
x_289 = l_instDecidableRelLe___rarg(x_286, x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_17);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_18);
return x_292;
}
else
{
lean_object* x_293; 
x_293 = lean_box(0);
x_20 = x_293;
goto block_277;
}
}
}
else
{
uint8_t x_294; 
x_294 = l_Lake_Monitor_reportJob___lambda__2___closed__8;
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_17);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_18);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_298 = l_Lake_instOrdJobAction;
x_299 = lean_box(x_12);
x_300 = lean_box(x_4);
x_301 = l_instDecidableRelLe___rarg(x_298, x_299, x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_302 = lean_box(0);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_17);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_18);
return x_304;
}
else
{
lean_object* x_305; 
x_305 = lean_box(0);
x_20 = x_305;
goto block_277;
}
}
}
}
}
block_323:
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
lean_dec(x_307);
x_308 = lean_array_get_size(x_1);
x_309 = lean_unsigned_to_nat(0u);
x_310 = lean_nat_dec_eq(x_308, x_309);
lean_dec(x_308);
x_311 = l_instDecidableNot___rarg(x_310);
if (x_311 == 0)
{
lean_object* x_312; 
x_312 = lean_box(0);
x_278 = x_312;
goto block_306;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_313 = l_Lake_instOrdLogLevel;
x_314 = lean_box(x_10);
x_315 = lean_box(x_9);
x_316 = l_instDecidableRelLe___rarg(x_313, x_314, x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = lean_box(x_6);
x_318 = lean_box(x_9);
x_319 = l_instDecidableRelLe___rarg(x_313, x_317, x_318);
if (x_319 == 0)
{
lean_object* x_320; 
x_320 = lean_box(0);
x_278 = x_320;
goto block_306;
}
else
{
lean_object* x_321; 
x_321 = lean_box(0);
x_20 = x_321;
goto block_277;
}
}
else
{
lean_object* x_322; 
x_322 = lean_box(0);
x_20 = x_322;
goto block_277;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_51 = lean_task_get_own(x_18);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
x_21 = x_53;
x_22 = x_54;
goto block_50;
block_50:
{
uint8_t x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_23 = l_Lake_Log_maxLv(x_21);
x_30 = lean_array_get_size(x_21);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
x_33 = l_instDecidableNot___rarg(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = lean_box(0);
x_35 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_10, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_34, x_2, x_3, x_4);
lean_dec(x_19);
lean_dec(x_21);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = l_Lake_instOrdLogLevel;
x_37 = lean_box(x_13);
x_38 = lean_box(x_23);
x_39 = l_instDecidableRelLe___rarg(x_36, x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_box(0);
x_41 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_10, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_40, x_2, x_3, x_4);
lean_dec(x_19);
lean_dec(x_21);
return x_41;
}
else
{
if (x_20 == 0)
{
uint8_t x_42; 
x_42 = l_Lake_Monitor_reportJob___lambda__2___closed__7;
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = lean_box(0);
x_44 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_10, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_43, x_2, x_3, x_4);
lean_dec(x_19);
lean_dec(x_21);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_3);
x_45 = lean_box(0);
x_24 = x_45;
goto block_29;
}
}
else
{
uint8_t x_46; 
x_46 = l_Lake_Monitor_reportJob___lambda__2___closed__8;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = lean_box(0);
x_48 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_10, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_47, x_2, x_3, x_4);
lean_dec(x_19);
lean_dec(x_21);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_3);
x_49 = lean_box(0);
x_24 = x_49;
goto block_29;
}
}
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_inc(x_19);
x_25 = lean_array_push(x_6, x_19);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_7);
lean_ctor_set(x_26, 3, x_8);
lean_ctor_set(x_26, 4, x_9);
x_27 = lean_box(0);
x_28 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_10, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_27, x_2, x_26, x_4);
lean_dec(x_19);
lean_dec(x_21);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(x_1, x_10, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Monitor_reportJob___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__2___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = lean_unbox(x_9);
lean_dec(x_9);
x_23 = lean_unbox(x_10);
lean_dec(x_10);
x_24 = lean_unbox(x_11);
lean_dec(x_11);
x_25 = lean_unbox(x_12);
lean_dec(x_12);
x_26 = lean_unbox(x_13);
lean_dec(x_13);
x_27 = lean_unbox(x_14);
lean_dec(x_14);
x_28 = l_Lake_Monitor_reportJob___lambda__2(x_1, x_2, x_3, x_19, x_5, x_20, x_21, x_8, x_22, x_23, x_24, x_25, x_26, x_27, x_15, x_16, x_17, x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_1);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_io_get_task_state(x_13, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
switch (x_16) {
case 0:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_array_push(x_12, x_9);
lean_ctor_set(x_4, 1, x_18);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_7 = x_17;
goto _start;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
lean_inc(x_9);
x_23 = lean_array_push(x_11, x_9);
x_24 = lean_array_push(x_12, x_9);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_7 = x_22;
goto _start;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_4);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
lean_inc(x_5);
x_29 = l_Lake_Monitor_reportJob(x_9, x_5, x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_36, x_37);
lean_dec(x_36);
lean_ctor_set(x_32, 0, x_38);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 0, x_11);
x_39 = 1;
x_40 = lean_usize_add(x_2, x_39);
x_2 = x_40;
x_4 = x_30;
x_6 = x_32;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
x_44 = lean_ctor_get(x_32, 2);
x_45 = lean_ctor_get(x_32, 3);
x_46 = lean_ctor_get(x_32, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_42, x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_46);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 0, x_11);
x_50 = 1;
x_51 = lean_usize_add(x_2, x_50);
x_2 = x_51;
x_4 = x_30;
x_6 = x_49;
x_7 = x_34;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; 
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_dec(x_30);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
lean_dec(x_29);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 4);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_55, x_61);
lean_dec(x_55);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 5, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
lean_ctor_set(x_63, 2, x_57);
lean_ctor_set(x_63, 3, x_58);
lean_ctor_set(x_63, 4, x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_11);
lean_ctor_set(x_64, 1, x_12);
x_65 = 1;
x_66 = lean_usize_add(x_2, x_65);
x_2 = x_66;
x_4 = x_64;
x_6 = x_63;
x_7 = x_54;
goto _start;
}
}
else
{
uint8_t x_68; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_29);
if (x_68 == 0)
{
return x_29;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_29, 0);
x_70 = lean_ctor_get(x_29, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_29);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
uint8_t x_72; 
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_72 = !lean_is_exclusive(x_14);
if (x_72 == 0)
{
return x_14;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_14, 0);
x_74 = lean_ctor_get(x_14, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_14);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_4, 0);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_4);
x_78 = lean_ctor_get(x_9, 0);
lean_inc(x_78);
x_79 = lean_io_get_task_state(x_78, x_7);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
switch (x_81) {
case 0:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_array_push(x_77, x_9);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
x_85 = 1;
x_86 = lean_usize_add(x_2, x_85);
x_2 = x_86;
x_4 = x_84;
x_7 = x_82;
goto _start;
}
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; size_t x_92; size_t x_93; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
lean_inc(x_9);
x_89 = lean_array_push(x_76, x_9);
x_90 = lean_array_push(x_77, x_9);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = 1;
x_93 = lean_usize_add(x_2, x_92);
x_2 = x_93;
x_4 = x_91;
x_7 = x_88;
goto _start;
}
default: 
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_dec(x_79);
lean_inc(x_5);
x_96 = l_Lake_Monitor_reportJob(x_9, x_5, x_6, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 4);
lean_inc(x_105);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 lean_ctor_release(x_98, 4);
 x_106 = x_98;
} else {
 lean_dec_ref(x_98);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_101, x_107);
lean_dec(x_101);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_102);
lean_ctor_set(x_109, 2, x_103);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set(x_109, 4, x_105);
if (lean_is_scalar(x_99)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_99;
}
lean_ctor_set(x_110, 0, x_76);
lean_ctor_set(x_110, 1, x_77);
x_111 = 1;
x_112 = lean_usize_add(x_2, x_111);
x_2 = x_112;
x_4 = x_110;
x_6 = x_109;
x_7 = x_100;
goto _start;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_5);
x_114 = lean_ctor_get(x_96, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_96, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_116 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_118 = lean_ctor_get(x_79, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_79, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_120 = x_79;
} else {
 lean_dec_ref(x_79);
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
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_5);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_4);
lean_ctor_set(x_122, 1, x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_7);
return x_123;
}
}
}
static lean_object* _init_l_Lake_Monitor_poll___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkBuildContext___closed__1;
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
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = l_Lake_Monitor_poll___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_5, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
x_12 = l_Lake_Monitor_poll___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_17 = l_Lake_Monitor_poll___closed__1;
x_18 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_1, x_15, x_16, x_17, x_2, x_3, x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_mono_ms_now(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_3, 3);
lean_dec(x_9);
lean_ctor_set(x_3, 3, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_26 = x_3;
} else {
 lean_dec_ref(x_3);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 5, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lake_Monitor_sleep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Monitor_sleep___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_mono_ms_now(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_nat_sub(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lake_Monitor_sleep___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = lean_apply_4(x_11, x_14, x_1, x_2, x_6);
return x_15;
}
else
{
uint32_t x_16; lean_object* x_17; 
x_16 = lean_uint32_of_nat(x_10);
lean_dec(x_10);
x_17 = l_IO_sleep(x_16, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_apply_4(x_11, x_18, x_1, x_2, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Monitor_sleep___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
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
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
lean_dec(x_15);
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
lean_object* x_19; 
lean_free_object(x_7);
lean_free_object(x_5);
lean_inc(x_2);
x_19 = l_Lake_Monitor_renderProgress(x_13, x_14, lean_box(0), x_2, x_11, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_2);
x_23 = l_Lake_Monitor_sleep(x_2, x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_2);
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
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_array_get_size(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_11);
lean_ctor_set(x_5, 0, x_42);
return x_5;
}
else
{
lean_object* x_43; 
lean_free_object(x_5);
lean_inc(x_2);
x_43 = l_Lake_Monitor_renderProgress(x_36, x_37, lean_box(0), x_2, x_11, x_9);
lean_dec(x_36);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_2);
x_47 = l_Lake_Monitor_sleep(x_2, x_46, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_1 = x_37;
x_3 = x_50;
x_4 = x_49;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_2);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
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
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_2);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_58 = x_43;
} else {
 lean_dec_ref(x_43);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
lean_dec(x_5);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_dec(x_6);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_64 = x_7;
} else {
 lean_dec_ref(x_7);
 x_64 = lean_box(0);
}
x_65 = lean_array_get_size(x_63);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_lt(x_66, x_65);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_2);
x_68 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_64);
lean_inc(x_2);
x_71 = l_Lake_Monitor_renderProgress(x_62, x_63, lean_box(0), x_2, x_61, x_60);
lean_dec(x_62);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_2);
x_75 = l_Lake_Monitor_sleep(x_2, x_74, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_1 = x_63;
x_3 = x_78;
x_4 = x_77;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_63);
lean_dec(x_2);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_63);
lean_dec(x_2);
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_86 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_88; 
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_5);
if (x_88 == 0)
{
return x_5;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_5);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lake_Monitor_loop(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_8, 2);
x_15 = l_Lake_print_x21___closed__11;
lean_ctor_set(x_8, 2, x_15);
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_5);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_inc(x_14);
x_21 = lean_apply_2(x_20, x_14, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_apply_1(x_23, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_6, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_24, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_6, 0, x_32);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
lean_ctor_set(x_6, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_io_error_to_string(x_36);
x_39 = l_Lake_print_x21___closed__9;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lake_print_x21___closed__10;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_String_quote(x_14);
lean_dec(x_14);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Std_Format_defWidth;
x_46 = lean_format_pretty(x_44, x_45, x_17, x_17);
x_47 = lean_string_append(x_42, x_46);
lean_dec(x_46);
x_48 = lean_string_append(x_47, x_15);
x_49 = l_Lake_print_x21___closed__12;
x_50 = l_Lake_print_x21___closed__13;
x_51 = lean_unsigned_to_nat(75u);
x_52 = lean_unsigned_to_nat(4u);
x_53 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_49, x_50, x_51, x_52, x_48);
lean_dec(x_48);
x_54 = l_panic___at_Lake_print_x21___spec__1(x_53, x_37);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
lean_dec(x_19);
x_57 = lean_apply_1(x_56, x_55);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set(x_6, 0, x_59);
lean_ctor_set(x_57, 0, x_6);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set(x_6, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_57, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_6, 0, x_65);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_6);
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_box(0);
lean_ctor_set(x_6, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_6);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_19);
lean_dec(x_8);
lean_free_object(x_6);
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_14);
lean_dec(x_2);
x_73 = lean_box(0);
lean_ctor_set(x_6, 0, x_73);
return x_5;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
x_76 = lean_ctor_get(x_8, 2);
x_77 = lean_ctor_get(x_8, 3);
x_78 = lean_ctor_get(x_8, 4);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_79 = l_Lake_print_x21___closed__11;
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set(x_80, 3, x_77);
lean_ctor_set(x_80, 4, x_78);
x_81 = lean_string_utf8_byte_size(x_76);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_nat_dec_eq(x_81, x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_5);
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_ctor_get(x_84, 4);
lean_inc(x_85);
lean_inc(x_76);
x_86 = lean_apply_2(x_85, x_76, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_76);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_apply_1(x_88, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
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
lean_ctor_set(x_6, 1, x_80);
lean_ctor_set(x_6, 0, x_90);
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_6);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_95 = x_89;
} else {
 lean_dec_ref(x_89);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
lean_ctor_set(x_6, 1, x_80);
lean_ctor_set(x_6, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
 lean_ctor_set_tag(x_97, 0);
}
lean_ctor_set(x_97, 0, x_6);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_86, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_86, 1);
lean_inc(x_99);
lean_dec(x_86);
x_100 = lean_io_error_to_string(x_98);
x_101 = l_Lake_print_x21___closed__9;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = l_Lake_print_x21___closed__10;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_String_quote(x_76);
lean_dec(x_76);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Std_Format_defWidth;
x_108 = lean_format_pretty(x_106, x_107, x_82, x_82);
x_109 = lean_string_append(x_104, x_108);
lean_dec(x_108);
x_110 = lean_string_append(x_109, x_79);
x_111 = l_Lake_print_x21___closed__12;
x_112 = l_Lake_print_x21___closed__13;
x_113 = lean_unsigned_to_nat(75u);
x_114 = lean_unsigned_to_nat(4u);
x_115 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_111, x_112, x_113, x_114, x_110);
lean_dec(x_110);
x_116 = l_panic___at_Lake_print_x21___spec__1(x_115, x_99);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_84, 0);
lean_inc(x_118);
lean_dec(x_84);
x_119 = lean_apply_1(x_118, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_80);
lean_ctor_set(x_6, 0, x_120);
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_6);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_125 = x_119;
} else {
 lean_dec_ref(x_119);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
lean_ctor_set(x_6, 1, x_80);
lean_ctor_set(x_6, 0, x_126);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
 lean_ctor_set_tag(x_127, 0);
}
lean_ctor_set(x_127, 0, x_6);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_84);
lean_dec(x_80);
lean_free_object(x_6);
x_128 = lean_ctor_get(x_116, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_116, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_130 = x_116;
} else {
 lean_dec_ref(x_116);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
lean_object* x_132; 
lean_dec(x_76);
lean_dec(x_2);
x_132 = lean_box(0);
lean_ctor_set(x_6, 1, x_80);
lean_ctor_set(x_6, 0, x_132);
return x_5;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_133 = lean_ctor_get(x_5, 1);
lean_inc(x_133);
lean_dec(x_5);
x_134 = lean_ctor_get(x_8, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_8, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_8, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_8, 4);
lean_inc(x_138);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 x_139 = x_8;
} else {
 lean_dec_ref(x_8);
 x_139 = lean_box(0);
}
x_140 = l_Lake_print_x21___closed__11;
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(0, 5, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_135);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_137);
lean_ctor_set(x_141, 4, x_138);
x_142 = lean_string_utf8_byte_size(x_136);
x_143 = lean_unsigned_to_nat(0u);
x_144 = lean_nat_dec_eq(x_142, x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_2, 1);
lean_inc(x_145);
lean_dec(x_2);
x_146 = lean_ctor_get(x_145, 4);
lean_inc(x_146);
lean_inc(x_136);
x_147 = lean_apply_2(x_146, x_136, x_133);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_136);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
lean_dec(x_145);
x_150 = lean_apply_1(x_149, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
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
lean_ctor_set(x_6, 1, x_141);
lean_ctor_set(x_6, 0, x_151);
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_6);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_156 = x_150;
} else {
 lean_dec_ref(x_150);
 x_156 = lean_box(0);
}
x_157 = lean_box(0);
lean_ctor_set(x_6, 1, x_141);
lean_ctor_set(x_6, 0, x_157);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
 lean_ctor_set_tag(x_158, 0);
}
lean_ctor_set(x_158, 0, x_6);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_159 = lean_ctor_get(x_147, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_147, 1);
lean_inc(x_160);
lean_dec(x_147);
x_161 = lean_io_error_to_string(x_159);
x_162 = l_Lake_print_x21___closed__9;
x_163 = lean_string_append(x_162, x_161);
lean_dec(x_161);
x_164 = l_Lake_print_x21___closed__10;
x_165 = lean_string_append(x_163, x_164);
x_166 = l_String_quote(x_136);
lean_dec(x_136);
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l_Std_Format_defWidth;
x_169 = lean_format_pretty(x_167, x_168, x_143, x_143);
x_170 = lean_string_append(x_165, x_169);
lean_dec(x_169);
x_171 = lean_string_append(x_170, x_140);
x_172 = l_Lake_print_x21___closed__12;
x_173 = l_Lake_print_x21___closed__13;
x_174 = lean_unsigned_to_nat(75u);
x_175 = lean_unsigned_to_nat(4u);
x_176 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_172, x_173, x_174, x_175, x_171);
lean_dec(x_171);
x_177 = l_panic___at_Lake_print_x21___spec__1(x_176, x_160);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_ctor_get(x_145, 0);
lean_inc(x_179);
lean_dec(x_145);
x_180 = lean_apply_1(x_179, x_178);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_141);
lean_ctor_set(x_6, 0, x_181);
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_6);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
x_187 = lean_box(0);
lean_ctor_set(x_6, 1, x_141);
lean_ctor_set(x_6, 0, x_187);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
 lean_ctor_set_tag(x_188, 0);
}
lean_ctor_set(x_188, 0, x_6);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_145);
lean_dec(x_141);
lean_free_object(x_6);
x_189 = lean_ctor_get(x_177, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_177, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_191 = x_177;
} else {
 lean_dec_ref(x_177);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_136);
lean_dec(x_2);
x_193 = lean_box(0);
lean_ctor_set(x_6, 1, x_141);
lean_ctor_set(x_6, 0, x_193);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_6);
lean_ctor_set(x_194, 1, x_133);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_195 = lean_ctor_get(x_6, 1);
lean_inc(x_195);
lean_dec(x_6);
x_196 = lean_ctor_get(x_5, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_197 = x_5;
} else {
 lean_dec_ref(x_5);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_195, 4);
lean_inc(x_202);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 x_203 = x_195;
} else {
 lean_dec_ref(x_195);
 x_203 = lean_box(0);
}
x_204 = l_Lake_print_x21___closed__11;
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 5, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_199);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_201);
lean_ctor_set(x_205, 4, x_202);
x_206 = lean_string_utf8_byte_size(x_200);
x_207 = lean_unsigned_to_nat(0u);
x_208 = lean_nat_dec_eq(x_206, x_207);
lean_dec(x_206);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_197);
x_209 = lean_ctor_get(x_2, 1);
lean_inc(x_209);
lean_dec(x_2);
x_210 = lean_ctor_get(x_209, 4);
lean_inc(x_210);
lean_inc(x_200);
x_211 = lean_apply_2(x_210, x_200, x_196);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_200);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
lean_dec(x_209);
x_214 = lean_apply_1(x_213, x_212);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_205);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
x_222 = lean_box(0);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_205);
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_221;
 lean_ctor_set_tag(x_224, 0);
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_220);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_225 = lean_ctor_get(x_211, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_211, 1);
lean_inc(x_226);
lean_dec(x_211);
x_227 = lean_io_error_to_string(x_225);
x_228 = l_Lake_print_x21___closed__9;
x_229 = lean_string_append(x_228, x_227);
lean_dec(x_227);
x_230 = l_Lake_print_x21___closed__10;
x_231 = lean_string_append(x_229, x_230);
x_232 = l_String_quote(x_200);
lean_dec(x_200);
x_233 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = l_Std_Format_defWidth;
x_235 = lean_format_pretty(x_233, x_234, x_207, x_207);
x_236 = lean_string_append(x_231, x_235);
lean_dec(x_235);
x_237 = lean_string_append(x_236, x_204);
x_238 = l_Lake_print_x21___closed__12;
x_239 = l_Lake_print_x21___closed__13;
x_240 = lean_unsigned_to_nat(75u);
x_241 = lean_unsigned_to_nat(4u);
x_242 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_238, x_239, x_240, x_241, x_237);
lean_dec(x_237);
x_243 = l_panic___at_Lake_print_x21___spec__1(x_242, x_226);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_ctor_get(x_209, 0);
lean_inc(x_245);
lean_dec(x_209);
x_246 = lean_apply_1(x_245, x_244);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_205);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_253 = x_246;
} else {
 lean_dec_ref(x_246);
 x_253 = lean_box(0);
}
x_254 = lean_box(0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_205);
if (lean_is_scalar(x_253)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_253;
 lean_ctor_set_tag(x_256, 0);
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_252);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_209);
lean_dec(x_205);
x_257 = lean_ctor_get(x_243, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_243, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_259 = x_243;
} else {
 lean_dec_ref(x_243);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_200);
lean_dec(x_2);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_205);
if (lean_is_scalar(x_197)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_197;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_196);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_2);
x_264 = !lean_is_exclusive(x_5);
if (x_264 == 0)
{
return x_5;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_5, 0);
x_266 = lean_ctor_get(x_5, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_5);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 3, 6);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_3);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 5, x_8);
x_15 = lean_io_mono_ms_now(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_19);
x_21 = l_Lake_Monitor_main(x_1, x_14, x_20, x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l_Lake_monitorJobs(x_1, x_2, x_14, x_15, x_16, x_17, x_18, x_19, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("- ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_Monitor_reportJob___lambda__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_apply_2(x_13, x_12, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_io_error_to_string(x_20);
x_23 = l_Lake_print_x21___closed__9;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lake_print_x21___closed__10;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_String_quote(x_12);
lean_dec(x_12);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Std_Format_defWidth;
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_format_pretty(x_28, x_29, x_30, x_30);
x_32 = lean_string_append(x_26, x_31);
lean_dec(x_31);
x_33 = l_Lake_print_x21___closed__11;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lake_print_x21___closed__12;
x_36 = l_Lake_print_x21___closed__13;
x_37 = lean_unsigned_to_nat(75u);
x_38 = lean_unsigned_to_nat(4u);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_34);
lean_dec(x_34);
x_40 = l_panic___at_Lake_print_x21___spec__1(x_39, x_21);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_3 = x_44;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
else
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_7);
x_10 = lean_array_uget(x_4, x_5);
lean_inc(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_3, x_2, x_8);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
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
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_45; 
x_45 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
x_58 = lean_get_set_stdout(x_46, x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
lean_ctor_set(x_49, 1, x_60);
lean_ctor_set(x_49, 0, x_56);
lean_ctor_set(x_50, 0, x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_53);
x_9 = x_61;
x_10 = x_59;
goto block_44;
}
else
{
uint8_t x_62; 
lean_free_object(x_50);
lean_dec(x_57);
lean_dec(x_56);
lean_free_object(x_49);
lean_dec(x_53);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_get_set_stdout(x_46, x_51);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
lean_ctor_set(x_49, 1, x_70);
lean_ctor_set(x_49, 0, x_66);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
x_9 = x_72;
x_10 = x_69;
goto block_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_49);
lean_dec(x_53);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_dec(x_49);
x_78 = lean_ctor_get(x_50, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_50, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_80 = x_50;
} else {
 lean_dec_ref(x_50);
 x_80 = lean_box(0);
}
x_81 = lean_get_set_stdout(x_46, x_51);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_9 = x_86;
x_10 = x_82;
goto block_44;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_dec(x_48);
x_92 = !lean_is_exclusive(x_49);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_49, 1);
x_94 = lean_ctor_get(x_49, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_50);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_50, 0);
x_97 = lean_ctor_get(x_50, 1);
x_98 = lean_get_set_stdout(x_46, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_9 = x_49;
x_10 = x_99;
goto block_44;
}
else
{
uint8_t x_100; 
lean_free_object(x_50);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_49);
lean_dec(x_93);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_50, 0);
x_105 = lean_ctor_get(x_50, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_50);
x_106 = lean_get_set_stdout(x_46, x_91);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_49, 0, x_108);
x_9 = x_49;
x_10 = x_107;
goto block_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_free_object(x_49);
lean_dec(x_93);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_49, 1);
lean_inc(x_113);
lean_dec(x_49);
x_114 = lean_ctor_get(x_50, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_50, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_116 = x_50;
} else {
 lean_dec_ref(x_50);
 x_116 = lean_box(0);
}
x_117 = lean_get_set_stdout(x_46, x_91);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
x_9 = x_120;
x_10 = x_118;
goto block_44;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_46);
x_125 = !lean_is_exclusive(x_48);
if (x_125 == 0)
{
return x_48;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_48, 0);
x_127 = lean_ctor_get(x_48, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_48);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
return x_45;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_45, 0);
x_131 = lean_ctor_get(x_45, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_45);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_44:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_17);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__4___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_45; 
x_45 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
x_58 = lean_get_set_stdin(x_46, x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
lean_ctor_set(x_49, 1, x_60);
lean_ctor_set(x_49, 0, x_56);
lean_ctor_set(x_50, 0, x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_53);
x_9 = x_61;
x_10 = x_59;
goto block_44;
}
else
{
uint8_t x_62; 
lean_free_object(x_50);
lean_dec(x_57);
lean_dec(x_56);
lean_free_object(x_49);
lean_dec(x_53);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_get_set_stdin(x_46, x_51);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
lean_ctor_set(x_49, 1, x_70);
lean_ctor_set(x_49, 0, x_66);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
x_9 = x_72;
x_10 = x_69;
goto block_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_49);
lean_dec(x_53);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_dec(x_49);
x_78 = lean_ctor_get(x_50, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_50, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_80 = x_50;
} else {
 lean_dec_ref(x_50);
 x_80 = lean_box(0);
}
x_81 = lean_get_set_stdin(x_46, x_51);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_9 = x_86;
x_10 = x_82;
goto block_44;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_dec(x_48);
x_92 = !lean_is_exclusive(x_49);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_49, 1);
x_94 = lean_ctor_get(x_49, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_50);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_50, 0);
x_97 = lean_ctor_get(x_50, 1);
x_98 = lean_get_set_stdin(x_46, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_9 = x_49;
x_10 = x_99;
goto block_44;
}
else
{
uint8_t x_100; 
lean_free_object(x_50);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_49);
lean_dec(x_93);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_50, 0);
x_105 = lean_ctor_get(x_50, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_50);
x_106 = lean_get_set_stdin(x_46, x_91);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_49, 0, x_108);
x_9 = x_49;
x_10 = x_107;
goto block_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_free_object(x_49);
lean_dec(x_93);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_49, 1);
lean_inc(x_113);
lean_dec(x_49);
x_114 = lean_ctor_get(x_50, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_50, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_116 = x_50;
} else {
 lean_dec_ref(x_50);
 x_116 = lean_box(0);
}
x_117 = lean_get_set_stdin(x_46, x_91);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
x_9 = x_120;
x_10 = x_118;
goto block_44;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_46);
x_125 = !lean_is_exclusive(x_48);
if (x_125 == 0)
{
return x_48;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_48, 0);
x_127 = lean_ctor_get(x_48, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_48);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
return x_45;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_45, 0);
x_131 = lean_ctor_get(x_45, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_45);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_44:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_17);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__5___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_45; 
x_45 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
x_58 = lean_get_set_stderr(x_46, x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
lean_ctor_set(x_49, 1, x_60);
lean_ctor_set(x_49, 0, x_56);
lean_ctor_set(x_50, 0, x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_53);
x_9 = x_61;
x_10 = x_59;
goto block_44;
}
else
{
uint8_t x_62; 
lean_free_object(x_50);
lean_dec(x_57);
lean_dec(x_56);
lean_free_object(x_49);
lean_dec(x_53);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_get_set_stderr(x_46, x_51);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
lean_ctor_set(x_49, 1, x_70);
lean_ctor_set(x_49, 0, x_66);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
x_9 = x_72;
x_10 = x_69;
goto block_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_49);
lean_dec(x_53);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_dec(x_49);
x_78 = lean_ctor_get(x_50, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_50, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_80 = x_50;
} else {
 lean_dec_ref(x_50);
 x_80 = lean_box(0);
}
x_81 = lean_get_set_stderr(x_46, x_51);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_9 = x_86;
x_10 = x_82;
goto block_44;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_dec(x_48);
x_92 = !lean_is_exclusive(x_49);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_49, 1);
x_94 = lean_ctor_get(x_49, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_50);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_50, 0);
x_97 = lean_ctor_get(x_50, 1);
x_98 = lean_get_set_stderr(x_46, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_9 = x_49;
x_10 = x_99;
goto block_44;
}
else
{
uint8_t x_100; 
lean_free_object(x_50);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_49);
lean_dec(x_93);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_50, 0);
x_105 = lean_ctor_get(x_50, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_50);
x_106 = lean_get_set_stderr(x_46, x_91);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_49, 0, x_108);
x_9 = x_49;
x_10 = x_107;
goto block_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_free_object(x_49);
lean_dec(x_93);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_49, 1);
lean_inc(x_113);
lean_dec(x_49);
x_114 = lean_ctor_get(x_50, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_50, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_116 = x_50;
} else {
 lean_dec_ref(x_50);
 x_116 = lean_box(0);
}
x_117 = lean_get_set_stderr(x_46, x_91);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
x_9 = x_120;
x_10 = x_118;
goto block_44;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_46);
x_125 = !lean_is_exclusive(x_48);
if (x_125 == 0)
{
return x_48;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_48, 0);
x_127 = lean_ctor_get(x_48, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_48);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
return x_45;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_45, 0);
x_131 = lean_ctor_get(x_45, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_45);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_44:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_17);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__6___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_45; 
x_45 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
x_58 = lean_get_set_stdout(x_46, x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
lean_ctor_set(x_49, 1, x_60);
lean_ctor_set(x_49, 0, x_56);
lean_ctor_set(x_50, 0, x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_53);
x_9 = x_61;
x_10 = x_59;
goto block_44;
}
else
{
uint8_t x_62; 
lean_free_object(x_50);
lean_dec(x_57);
lean_dec(x_56);
lean_free_object(x_49);
lean_dec(x_53);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_get_set_stdout(x_46, x_51);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
lean_ctor_set(x_49, 1, x_70);
lean_ctor_set(x_49, 0, x_66);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
x_9 = x_72;
x_10 = x_69;
goto block_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_49);
lean_dec(x_53);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_dec(x_49);
x_78 = lean_ctor_get(x_50, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_50, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_80 = x_50;
} else {
 lean_dec_ref(x_50);
 x_80 = lean_box(0);
}
x_81 = lean_get_set_stdout(x_46, x_51);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_9 = x_86;
x_10 = x_82;
goto block_44;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_dec(x_48);
x_92 = !lean_is_exclusive(x_49);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_49, 1);
x_94 = lean_ctor_get(x_49, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_50);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_50, 0);
x_97 = lean_ctor_get(x_50, 1);
x_98 = lean_get_set_stdout(x_46, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_9 = x_49;
x_10 = x_99;
goto block_44;
}
else
{
uint8_t x_100; 
lean_free_object(x_50);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_49);
lean_dec(x_93);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_50, 0);
x_105 = lean_ctor_get(x_50, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_50);
x_106 = lean_get_set_stdout(x_46, x_91);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_49, 0, x_108);
x_9 = x_49;
x_10 = x_107;
goto block_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_free_object(x_49);
lean_dec(x_93);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_49, 1);
lean_inc(x_113);
lean_dec(x_49);
x_114 = lean_ctor_get(x_50, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_50, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_116 = x_50;
} else {
 lean_dec_ref(x_50);
 x_116 = lean_box(0);
}
x_117 = lean_get_set_stdout(x_46, x_91);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
x_9 = x_120;
x_10 = x_118;
goto block_44;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_46);
x_125 = !lean_is_exclusive(x_48);
if (x_125 == 0)
{
return x_48;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_48, 0);
x_127 = lean_ctor_get(x_48, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_48);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
return x_45;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_45, 0);
x_131 = lean_ctor_get(x_45, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_45);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_44:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_17);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__7___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_45; 
x_45 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_ctor_get(x_49, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
x_58 = lean_get_set_stdin(x_46, x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
lean_ctor_set(x_49, 1, x_60);
lean_ctor_set(x_49, 0, x_56);
lean_ctor_set(x_50, 0, x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_53);
x_9 = x_61;
x_10 = x_59;
goto block_44;
}
else
{
uint8_t x_62; 
lean_free_object(x_50);
lean_dec(x_57);
lean_dec(x_56);
lean_free_object(x_49);
lean_dec(x_53);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_get_set_stdin(x_46, x_51);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_box(0);
lean_ctor_set(x_49, 1, x_70);
lean_ctor_set(x_49, 0, x_66);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
x_9 = x_72;
x_10 = x_69;
goto block_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_49);
lean_dec(x_53);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_49, 1);
lean_inc(x_77);
lean_dec(x_49);
x_78 = lean_ctor_get(x_50, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_50, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_80 = x_50;
} else {
 lean_dec_ref(x_50);
 x_80 = lean_box(0);
}
x_81 = lean_get_set_stdin(x_46, x_51);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
x_9 = x_86;
x_10 = x_82;
goto block_44;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_dec(x_48);
x_92 = !lean_is_exclusive(x_49);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_49, 1);
x_94 = lean_ctor_get(x_49, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_50);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_50, 0);
x_97 = lean_ctor_get(x_50, 1);
x_98 = lean_get_set_stdin(x_46, x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_9 = x_49;
x_10 = x_99;
goto block_44;
}
else
{
uint8_t x_100; 
lean_free_object(x_50);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_49);
lean_dec(x_93);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_50, 0);
x_105 = lean_ctor_get(x_50, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_50);
x_106 = lean_get_set_stdin(x_46, x_91);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_49, 0, x_108);
x_9 = x_49;
x_10 = x_107;
goto block_44;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_free_object(x_49);
lean_dec(x_93);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_49, 1);
lean_inc(x_113);
lean_dec(x_49);
x_114 = lean_ctor_get(x_50, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_50, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_116 = x_50;
} else {
 lean_dec_ref(x_50);
 x_116 = lean_box(0);
}
x_117 = lean_get_set_stdin(x_46, x_91);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
x_9 = x_120;
x_10 = x_118;
goto block_44;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_46);
x_125 = !lean_is_exclusive(x_48);
if (x_125 == 0)
{
return x_48;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_48, 0);
x_127 = lean_ctor_get(x_48, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_48);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
return x_45;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_45, 0);
x_131 = lean_ctor_get(x_45, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_45);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
block_44:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_17);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__8___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__3;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_mk_ref(x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_ofBuffer(x_11);
lean_inc(x_14);
x_17 = l_IO_FS_Stream_ofBuffer(x_14);
if (x_2 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__4___rarg), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__5___rarg(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
x_29 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_string_validate_utf8(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_34 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_35 = l_panic___at_String_fromUTF8_x21___spec__1(x_34);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_21, 0, x_20);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_string_from_utf8_unchecked(x_32);
lean_dec(x_32);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_37);
lean_ctor_set(x_21, 0, x_20);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_29, 0, x_38);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_string_validate_utf8(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
x_43 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_44 = l_panic___at_String_fromUTF8_x21___spec__1(x_43);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_44);
lean_ctor_set(x_21, 0, x_20);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_24);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_string_from_utf8_unchecked(x_41);
lean_dec(x_41);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_47);
lean_ctor_set(x_21, 0, x_20);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_24);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
x_56 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_string_validate_utf8(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_60);
x_62 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_63 = l_panic___at_String_fromUTF8_x21___spec__1(x_62);
lean_ctor_set(x_20, 1, x_54);
lean_ctor_set(x_20, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_20);
lean_ctor_set(x_64, 1, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_24);
if (lean_is_scalar(x_59)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_59;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_string_from_utf8_unchecked(x_60);
lean_dec(x_60);
lean_ctor_set(x_20, 1, x_54);
lean_ctor_set(x_20, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_20);
lean_ctor_set(x_68, 1, x_55);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_24);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_58);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_20);
lean_dec(x_24);
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_73 = x_56;
} else {
 lean_dec_ref(x_56);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_dec(x_20);
x_76 = lean_ctor_get(x_21, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_78 = x_21;
} else {
 lean_dec_ref(x_21);
 x_78 = lean_box(0);
}
x_79 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
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
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_string_validate_utf8(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
x_85 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_86 = l_panic___at_String_fromUTF8_x21___spec__1(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
if (lean_is_scalar(x_78)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_78;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_81);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_string_from_utf8_unchecked(x_83);
lean_dec(x_83);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_76);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_77);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_75);
if (lean_is_scalar(x_82)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_82;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_81);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
x_96 = lean_ctor_get(x_79, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_79, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_98 = x_79;
} else {
 lean_dec_ref(x_79);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_14);
x_100 = !lean_is_exclusive(x_19);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_19, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_20);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_20, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_21);
if (x_104 == 0)
{
return x_19;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_21, 0);
x_106 = lean_ctor_get(x_21, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_21);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_20, 0, x_107);
return x_19;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_20, 1);
lean_inc(x_108);
lean_dec(x_20);
x_109 = lean_ctor_get(x_21, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_21, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_111 = x_21;
} else {
 lean_dec_ref(x_21);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
lean_ctor_set(x_19, 0, x_113);
return x_19;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_19, 1);
lean_inc(x_114);
lean_dec(x_19);
x_115 = lean_ctor_get(x_20, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_116 = x_20;
} else {
 lean_dec_ref(x_20);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_21, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_21, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_119 = x_21;
} else {
 lean_dec_ref(x_21);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_116;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_115);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_114);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_14);
x_123 = !lean_is_exclusive(x_19);
if (x_123 == 0)
{
return x_19;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_19, 0);
x_125 = lean_ctor_get(x_19, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_19);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_inc(x_17);
x_127 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__6___rarg), 8, 2);
lean_closure_set(x_127, 0, x_17);
lean_closure_set(x_127, 1, x_1);
x_128 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__7___rarg), 8, 2);
lean_closure_set(x_128, 0, x_17);
lean_closure_set(x_128, 1, x_127);
x_129 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__8___rarg(x_16, x_128, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = !lean_is_exclusive(x_130);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_130, 1);
x_135 = lean_ctor_get(x_130, 0);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_131);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_131, 0);
x_138 = lean_ctor_get(x_131, 1);
x_139 = lean_st_ref_get(x_14, x_132);
lean_dec(x_14);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_string_validate_utf8(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_142);
x_144 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_145 = l_panic___at_String_fromUTF8_x21___spec__1(x_144);
lean_ctor_set(x_130, 1, x_137);
lean_ctor_set(x_130, 0, x_145);
lean_ctor_set(x_131, 0, x_130);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_131);
lean_ctor_set(x_146, 1, x_134);
lean_ctor_set(x_139, 0, x_146);
return x_139;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_string_from_utf8_unchecked(x_142);
lean_dec(x_142);
lean_ctor_set(x_130, 1, x_137);
lean_ctor_set(x_130, 0, x_147);
lean_ctor_set(x_131, 0, x_130);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_131);
lean_ctor_set(x_148, 1, x_134);
lean_ctor_set(x_139, 0, x_148);
return x_139;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_139, 0);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_139);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_string_validate_utf8(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_151);
x_153 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_154 = l_panic___at_String_fromUTF8_x21___spec__1(x_153);
lean_ctor_set(x_130, 1, x_137);
lean_ctor_set(x_130, 0, x_154);
lean_ctor_set(x_131, 0, x_130);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_131);
lean_ctor_set(x_155, 1, x_134);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_150);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_string_from_utf8_unchecked(x_151);
lean_dec(x_151);
lean_ctor_set(x_130, 1, x_137);
lean_ctor_set(x_130, 0, x_157);
lean_ctor_set(x_131, 0, x_130);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_131);
lean_ctor_set(x_158, 1, x_134);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_150);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_free_object(x_131);
lean_dec(x_138);
lean_dec(x_137);
lean_free_object(x_130);
lean_dec(x_134);
x_160 = !lean_is_exclusive(x_139);
if (x_160 == 0)
{
return x_139;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_139, 0);
x_162 = lean_ctor_get(x_139, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_139);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_131, 0);
x_165 = lean_ctor_get(x_131, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_131);
x_166 = lean_st_ref_get(x_14, x_132);
lean_dec(x_14);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_string_validate_utf8(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_170);
x_172 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_173 = l_panic___at_String_fromUTF8_x21___spec__1(x_172);
lean_ctor_set(x_130, 1, x_164);
lean_ctor_set(x_130, 0, x_173);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_130);
lean_ctor_set(x_174, 1, x_165);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_134);
if (lean_is_scalar(x_169)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_169;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_168);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_string_from_utf8_unchecked(x_170);
lean_dec(x_170);
lean_ctor_set(x_130, 1, x_164);
lean_ctor_set(x_130, 0, x_177);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_130);
lean_ctor_set(x_178, 1, x_165);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_134);
if (lean_is_scalar(x_169)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_169;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_168);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_165);
lean_dec(x_164);
lean_free_object(x_130);
lean_dec(x_134);
x_181 = lean_ctor_get(x_166, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_166, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_183 = x_166;
} else {
 lean_dec_ref(x_166);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_130, 1);
lean_inc(x_185);
lean_dec(x_130);
x_186 = lean_ctor_get(x_131, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_131, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_188 = x_131;
} else {
 lean_dec_ref(x_131);
 x_188 = lean_box(0);
}
x_189 = lean_st_ref_get(x_14, x_132);
lean_dec(x_14);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_190, 0);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_string_validate_utf8(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_193);
x_195 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5;
x_196 = l_panic___at_String_fromUTF8_x21___spec__1(x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_186);
if (lean_is_scalar(x_188)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_188;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_187);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_185);
if (lean_is_scalar(x_192)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_192;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_191);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_string_from_utf8_unchecked(x_193);
lean_dec(x_193);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_186);
if (lean_is_scalar(x_188)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_188;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_187);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_185);
if (lean_is_scalar(x_192)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_192;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_191);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
x_206 = lean_ctor_get(x_189, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_189, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_208 = x_189;
} else {
 lean_dec_ref(x_189);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_14);
x_210 = !lean_is_exclusive(x_129);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_129, 0);
lean_dec(x_211);
x_212 = !lean_is_exclusive(x_130);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_130, 0);
lean_dec(x_213);
x_214 = !lean_is_exclusive(x_131);
if (x_214 == 0)
{
return x_129;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_131, 0);
x_216 = lean_ctor_get(x_131, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_131);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_130, 0, x_217);
return x_129;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = lean_ctor_get(x_130, 1);
lean_inc(x_218);
lean_dec(x_130);
x_219 = lean_ctor_get(x_131, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_131, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_221 = x_131;
} else {
 lean_dec_ref(x_131);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_218);
lean_ctor_set(x_129, 0, x_223);
return x_129;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_224 = lean_ctor_get(x_129, 1);
lean_inc(x_224);
lean_dec(x_129);
x_225 = lean_ctor_get(x_130, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_226 = x_130;
} else {
 lean_dec_ref(x_130);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_131, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_131, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_229 = x_131;
} else {
 lean_dec_ref(x_131);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_225);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_224);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_14);
x_233 = !lean_is_exclusive(x_129);
if (x_233 == 0)
{
return x_129;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_129, 0);
x_235 = lean_ctor_get(x_129, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_129);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_13);
if (x_237 == 0)
{
return x_13;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_13, 0);
x_239 = lean_ctor_get(x_13, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_13);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_10);
if (x_241 == 0)
{
return x_10;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_10, 0);
x_243 = lean_ctor_get(x_10, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_10);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Some required builds logged failures:\n", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__5;
x_2 = l_Std_Format_defWidth;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("top-level build failed", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__7;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Computing build jobs", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__10;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_array_get_size(x_1);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_eq(x_95, x_96);
lean_dec(x_95);
x_98 = l_instDecidableNot___rarg(x_97);
x_99 = lean_ctor_get(x_2, 3);
x_100 = lean_st_ref_get(x_99, x_11);
if (x_98 == 0)
{
lean_object* x_145; 
x_145 = l_Lake_mkBuildContext___closed__1;
x_101 = x_145;
goto block_144;
}
else
{
uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_146 = l_Lake_Log_maxLv(x_1);
x_147 = l_Lake_instOrdLogLevel;
x_148 = lean_box(x_6);
x_149 = lean_box(x_146);
x_150 = l_instDecidableRelLe___rarg(x_147, x_148, x_149);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = l_Lake_mkBuildContext___closed__1;
x_101 = x_151;
goto block_144;
}
else
{
lean_object* x_152; 
x_152 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__11;
x_101 = x_152;
goto block_144;
}
}
block_94:
{
lean_object* x_14; uint8_t x_67; 
x_67 = l_Array_isEmpty___rarg(x_12);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_5, 4);
lean_inc(x_68);
x_69 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3;
x_70 = lean_apply_2(x_68, x_69, x_13);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_14 = x_71;
goto block_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_io_error_to_string(x_72);
x_75 = l_Lake_print_x21___closed__9;
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = l_Lake_print_x21___closed__10;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__6;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lake_print_x21___closed__11;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Lake_print_x21___closed__12;
x_84 = l_Lake_print_x21___closed__13;
x_85 = lean_unsigned_to_nat(75u);
x_86 = lean_unsigned_to_nat(4u);
x_87 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_83, x_84, x_85, x_86, x_82);
lean_dec(x_82);
x_88 = l_panic___at_Lake_print_x21___spec__1(x_87, x_73);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_14 = x_89;
goto block_66;
}
}
else
{
lean_dec(x_12);
lean_dec(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__8;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_13);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_9, 0);
lean_inc(x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_13);
return x_93;
}
}
block_66:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_12);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_apply_1(x_18, x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_15, x_15);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
lean_dec(x_12);
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_apply_1(x_33, x_14);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
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
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_43 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_49 = lean_box(0);
lean_inc(x_5);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1(x_5, x_12, x_47, x_48, x_49, x_14);
lean_dec(x_12);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
lean_dec(x_5);
x_53 = lean_apply_1(x_52, x_51);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_53, 0);
lean_dec(x_61);
x_62 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set(x_53, 0, x_62);
return x_53;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_dec(x_53);
x_64 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
}
block_144:
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_105 = 2;
x_106 = l_Lake_instDecidableEqVerbosity(x_104, x_105);
x_107 = lean_array_get_size(x_102);
if (x_4 == 0)
{
if (x_106 == 0)
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = 2;
x_109 = l_Lake_print_x21___closed__11;
x_110 = lean_unsigned_to_nat(100u);
lean_inc(x_5);
x_111 = l_Lake_monitorJobs(x_102, x_5, x_6, x_7, x_108, x_106, x_8, x_4, x_109, x_101, x_107, x_110, x_103);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_12 = x_112;
x_13 = x_113;
goto block_94;
}
else
{
uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = 0;
x_115 = l_Lake_print_x21___closed__11;
x_116 = lean_unsigned_to_nat(100u);
lean_inc(x_5);
x_117 = l_Lake_monitorJobs(x_102, x_5, x_6, x_7, x_114, x_106, x_8, x_4, x_115, x_101, x_107, x_116, x_103);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_12 = x_118;
x_13 = x_119;
goto block_94;
}
}
else
{
if (x_8 == 0)
{
if (x_106 == 0)
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = 2;
x_121 = l_Lake_print_x21___closed__11;
x_122 = lean_unsigned_to_nat(100u);
lean_inc(x_5);
x_123 = l_Lake_monitorJobs(x_102, x_5, x_6, x_7, x_120, x_106, x_8, x_4, x_121, x_101, x_107, x_122, x_103);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_12 = x_124;
x_13 = x_125;
goto block_94;
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = 0;
x_127 = l_Lake_print_x21___closed__11;
x_128 = lean_unsigned_to_nat(100u);
lean_inc(x_5);
x_129 = l_Lake_monitorJobs(x_102, x_5, x_6, x_7, x_126, x_106, x_8, x_4, x_127, x_101, x_107, x_128, x_103);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_12 = x_130;
x_13 = x_131;
goto block_94;
}
}
else
{
if (x_106 == 0)
{
uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = 2;
x_133 = l_Lake_Ansi_resetLine;
x_134 = lean_unsigned_to_nat(100u);
lean_inc(x_5);
x_135 = l_Lake_monitorJobs(x_102, x_5, x_6, x_7, x_132, x_106, x_8, x_4, x_133, x_101, x_107, x_134, x_103);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_12 = x_136;
x_13 = x_137;
goto block_94;
}
else
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = 0;
x_139 = l_Lake_Ansi_resetLine;
x_140 = lean_unsigned_to_nat(100u);
lean_inc(x_5);
x_141 = l_Lake_monitorJobs(x_102, x_5, x_6, x_7, x_138, x_106, x_8, x_4, x_139, x_101, x_107, x_140, x_103);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_12 = x_142;
x_13 = x_143;
goto block_94;
}
}
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Monitor_reportJob___lambda__2___closed__2;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2;
x_2 = l_Std_Format_defWidth;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_1, 4);
lean_inc(x_46);
x_47 = l_Lake_Monitor_reportJob___lambda__2___closed__2;
x_48 = lean_apply_2(x_46, x_47, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_10 = x_49;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_io_error_to_string(x_50);
x_53 = l_Lake_print_x21___closed__9;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lake_print_x21___closed__10;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = l_Lake_print_x21___closed__11;
x_60 = lean_string_append(x_58, x_59);
x_61 = l_Lake_print_x21___closed__12;
x_62 = l_Lake_print_x21___closed__13;
x_63 = lean_unsigned_to_nat(75u);
x_64 = lean_unsigned_to_nat(4u);
x_65 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_61, x_62, x_63, x_64, x_60);
lean_dec(x_60);
x_66 = l_panic___at_Lake_print_x21___spec__1(x_65, x_51);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_10 = x_67;
goto block_45;
}
block_45:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_2);
if (x_6 == 0)
{
x_13 = x_7;
goto block_43;
}
else
{
uint8_t x_44; 
x_44 = 0;
x_13 = x_44;
goto block_43;
}
block_43:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_2(x_3, x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_3, x_20, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_2, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_1(x_23, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_apply_2(x_3, x_25, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_apply_2(x_3, x_29, x_28);
return x_30;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_2);
x_33 = lean_box(0);
lean_inc(x_1);
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__2(x_1, x_4, x_13, x_5, x_31, x_32, x_33, x_10);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_apply_1(x_36, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_apply_2(x_3, x_38, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_apply_2(x_3, x_33, x_41);
return x_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1;
x_14 = lean_string_append(x_13, x_8);
lean_dec(x_8);
x_15 = l_Lake_print_x21___closed__11;
x_16 = lean_string_append(x_14, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_push(x_5, x_18);
x_20 = lean_box(0);
x_21 = l_Lake_Workspace_runFetchM___rarg___lambda__3(x_9, x_20, x_2, x_3, x_4, x_19, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = l_Lake_Workspace_runFetchM___rarg___lambda__3(x_9, x_22, x_2, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" [\?/\?] ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_print_x21___closed__11;
x_2 = l_Lake_Ansi_resetLine;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__2;
x_2 = l_Lake_print_x21___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg___lambda__4___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_recFetch___at_Lake_FetchM_run___spec__7), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_148 = 1;
x_149 = lean_box(x_148);
x_150 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___boxed), 8, 2);
lean_closure_set(x_150, 0, x_1);
lean_closure_set(x_150, 1, x_149);
x_151 = lean_box(0);
x_152 = lean_box(0);
x_153 = l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__4;
x_154 = l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__5;
x_155 = l_Lake_mkBuildContext___closed__1;
lean_inc(x_2);
x_156 = l_Lake_EquipT_bind___at_Lake_LeanExe_recBuildExe___spec__7___rarg(x_150, x_153, x_154, x_151, x_2, x_155, x_152, x_10);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = lean_ctor_get(x_157, 1);
lean_dec(x_160);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_dec(x_156);
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_157, 1, x_163);
lean_ctor_set(x_157, 0, x_164);
x_11 = x_157;
x_12 = x_161;
goto block_147;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_156, 1);
lean_inc(x_165);
lean_dec(x_156);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_dec(x_159);
x_167 = lean_box(0);
lean_ctor_set(x_157, 1, x_166);
lean_ctor_set(x_157, 0, x_167);
x_11 = x_157;
x_12 = x_165;
goto block_147;
}
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_157, 0);
lean_inc(x_168);
lean_dec(x_157);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
lean_dec(x_156);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_11 = x_173;
x_12 = x_169;
goto block_147;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_156, 1);
lean_inc(x_174);
lean_dec(x_156);
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
lean_dec(x_168);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_11 = x_177;
x_12 = x_174;
goto block_147;
}
}
block_147:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(x_5);
x_16 = lean_box(x_6);
x_17 = lean_box(x_7);
x_18 = lean_box(x_8);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_14);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg___lambda__1___boxed), 11, 9);
lean_closure_set(x_19, 0, x_14);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_4);
lean_closure_set(x_19, 3, x_15);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_16);
lean_closure_set(x_19, 6, x_17);
lean_closure_set(x_19, 7, x_18);
lean_closure_set(x_19, 8, x_13);
x_20 = lean_array_get_size(x_14);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
x_23 = l_instDecidableNot___rarg(x_22);
if (x_23 == 0)
{
uint8_t x_145; 
x_145 = 0;
x_24 = x_145;
goto block_144;
}
else
{
uint8_t x_146; 
x_146 = 1;
x_24 = x_146;
goto block_144;
}
block_144:
{
uint8_t x_25; 
if (x_24 == 0)
{
uint8_t x_136; 
x_136 = 0;
x_25 = x_136;
goto block_135;
}
else
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = l_Lake_Log_maxLv(x_14);
x_138 = l_Lake_instOrdLogLevel;
x_139 = lean_box(x_6);
x_140 = lean_box(x_137);
x_141 = l_instDecidableRelLe___rarg(x_138, x_139, x_140);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = 0;
x_25 = x_142;
goto block_135;
}
else
{
uint8_t x_143; 
x_143 = 1;
x_25 = x_143;
goto block_135;
}
}
block_135:
{
lean_object* x_26; 
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_20);
lean_dec(x_19);
x_124 = lean_box(0);
x_125 = l_Lake_Workspace_runFetchM___rarg___lambda__1(x_14, x_2, x_4, x_5, x_3, x_6, x_7, x_8, x_13, x_124, x_12);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_14);
return x_125;
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = l_Lake_Log_maxLv(x_14);
x_127 = l_Lake_instOrdLogLevel;
x_128 = lean_box(x_7);
x_129 = lean_box(x_126);
x_130 = l_instDecidableRelLe___rarg(x_127, x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_20);
lean_dec(x_19);
x_131 = lean_box(0);
x_132 = l_Lake_Workspace_runFetchM___rarg___lambda__1(x_14, x_2, x_4, x_5, x_3, x_6, x_7, x_8, x_13, x_131, x_12);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_14);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_133 = lean_box(0);
x_26 = x_133;
goto block_123;
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_134 = lean_box(0);
x_26 = x_134;
goto block_123;
}
block_123:
{
uint8_t x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_27 = l_Lake_Log_maxLv(x_14);
x_28 = l_Lake_LogLevel_icon(x_27);
x_29 = l_Lake_print_x21___closed__11;
x_30 = lean_string_push(x_29, x_28);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_29);
if (x_8 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_3, 4);
lean_inc(x_37);
lean_inc(x_36);
x_38 = lean_apply_2(x_37, x_36, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_3, x_20, x_19, x_8, x_14, x_25, x_7, x_39, x_40);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_20);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_io_error_to_string(x_42);
x_45 = l_Lake_print_x21___closed__9;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lake_print_x21___closed__10;
x_48 = lean_string_append(x_46, x_47);
x_49 = l_String_quote(x_36);
lean_dec(x_36);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Std_Format_defWidth;
x_52 = lean_format_pretty(x_50, x_51, x_21, x_21);
x_53 = lean_string_append(x_48, x_52);
lean_dec(x_52);
x_54 = lean_string_append(x_53, x_29);
x_55 = l_Lake_print_x21___closed__12;
x_56 = l_Lake_print_x21___closed__13;
x_57 = lean_unsigned_to_nat(75u);
x_58 = lean_unsigned_to_nat(4u);
x_59 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_55, x_56, x_57, x_58, x_54);
lean_dec(x_54);
x_60 = l_panic___at_Lake_print_x21___spec__1(x_59, x_43);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_3, x_20, x_19, x_8, x_14, x_25, x_7, x_61, x_62);
lean_dec(x_61);
lean_dec(x_14);
lean_dec(x_20);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lake_LogLevel_ansiColor(x_27);
x_65 = l_Lake_Ansi_chalk(x_64, x_36);
lean_dec(x_36);
lean_dec(x_64);
if (x_5 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_3, 4);
lean_inc(x_66);
lean_inc(x_65);
x_67 = lean_apply_2(x_66, x_65, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_3, x_20, x_19, x_8, x_14, x_25, x_7, x_68, x_69);
lean_dec(x_68);
lean_dec(x_14);
lean_dec(x_20);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_io_error_to_string(x_71);
x_74 = l_Lake_print_x21___closed__9;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lake_print_x21___closed__10;
x_77 = lean_string_append(x_75, x_76);
x_78 = l_String_quote(x_65);
lean_dec(x_65);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Std_Format_defWidth;
x_81 = lean_format_pretty(x_79, x_80, x_21, x_21);
x_82 = lean_string_append(x_77, x_81);
lean_dec(x_81);
x_83 = lean_string_append(x_82, x_29);
x_84 = l_Lake_print_x21___closed__12;
x_85 = l_Lake_print_x21___closed__13;
x_86 = lean_unsigned_to_nat(75u);
x_87 = lean_unsigned_to_nat(4u);
x_88 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_84, x_85, x_86, x_87, x_83);
lean_dec(x_83);
x_89 = l_panic___at_Lake_print_x21___spec__1(x_88, x_72);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_3, x_20, x_19, x_8, x_14, x_25, x_7, x_90, x_91);
lean_dec(x_90);
lean_dec(x_14);
lean_dec(x_20);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__3;
x_94 = lean_string_append(x_93, x_65);
lean_dec(x_65);
x_95 = lean_string_append(x_94, x_29);
x_96 = lean_ctor_get(x_3, 4);
lean_inc(x_96);
lean_inc(x_95);
x_97 = lean_apply_2(x_96, x_95, x_12);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_3, x_20, x_19, x_8, x_14, x_25, x_7, x_98, x_99);
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_20);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_dec(x_97);
x_103 = lean_io_error_to_string(x_101);
x_104 = l_Lake_print_x21___closed__9;
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
x_106 = l_Lake_print_x21___closed__10;
x_107 = lean_string_append(x_105, x_106);
x_108 = l_String_quote(x_95);
lean_dec(x_95);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_Std_Format_defWidth;
x_111 = lean_format_pretty(x_109, x_110, x_21, x_21);
x_112 = lean_string_append(x_107, x_111);
lean_dec(x_111);
x_113 = lean_string_append(x_112, x_29);
x_114 = l_Lake_print_x21___closed__12;
x_115 = l_Lake_print_x21___closed__13;
x_116 = lean_unsigned_to_nat(75u);
x_117 = lean_unsigned_to_nat(4u);
x_118 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_114, x_115, x_116, x_117, x_113);
lean_dec(x_113);
x_119 = l_panic___at_Lake_print_x21___spec__1(x_118, x_102);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_3, x_20, x_19, x_8, x_14, x_25, x_7, x_120, x_121);
lean_dec(x_120);
lean_dec(x_14);
lean_dec(x_20);
return x_122;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⣿ [\?/\?] ", 10, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__1;
x_2 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__2;
x_2 = l_Lake_print_x21___closed__11;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__3;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__5;
x_2 = l_Std_Format_defWidth;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lake_OutStream_get(x_5, x_4);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_inc(x_7);
x_10 = l_Lake_AnsiMode_isEnabled(x_7, x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_15 = l_Lake_BuildConfig_showProgress(x_3);
lean_inc(x_3);
x_16 = l_Lake_mkBuildContext(x_1, x_3, x_12);
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unbox(x_11);
lean_dec(x_11);
x_21 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_2, x_17, x_7, x_3, x_15, x_14, x_13, x_20, x_19, x_18);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_unbox(x_11);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = lean_unbox(x_11);
lean_dec(x_11);
x_27 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_2, x_23, x_7, x_3, x_15, x_14, x_13, x_26, x_25, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_ctor_get(x_7, 4);
lean_inc(x_30);
x_31 = l_Lake_Workspace_runFetchM___rarg___closed__3;
x_32 = lean_apply_2(x_30, x_31, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
x_35 = lean_apply_1(x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_11);
lean_dec(x_11);
x_39 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_2, x_28, x_7, x_3, x_15, x_14, x_13, x_38, x_36, x_37);
lean_dec(x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_unbox(x_11);
lean_dec(x_11);
x_43 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_2, x_28, x_7, x_3, x_15, x_14, x_13, x_42, x_41, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_io_error_to_string(x_44);
x_47 = l_Lake_print_x21___closed__9;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lake_print_x21___closed__10;
x_50 = lean_string_append(x_48, x_49);
x_51 = l_Lake_Workspace_runFetchM___rarg___closed__6;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Lake_print_x21___closed__11;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Lake_print_x21___closed__12;
x_56 = l_Lake_print_x21___closed__13;
x_57 = lean_unsigned_to_nat(75u);
x_58 = lean_unsigned_to_nat(4u);
x_59 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_55, x_56, x_57, x_58, x_54);
lean_dec(x_54);
x_60 = l_panic___at_Lake_print_x21___spec__1(x_59, x_45);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
x_63 = lean_apply_1(x_62, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unbox(x_11);
lean_dec(x_11);
x_67 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_2, x_28, x_7, x_3, x_15, x_14, x_13, x_66, x_64, x_65);
lean_dec(x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_box(0);
x_70 = lean_unbox(x_11);
lean_dec(x_11);
x_71 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_2, x_28, x_7, x_3, x_15, x_14, x_13, x_70, x_69, x_68);
return x_71;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__2(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lake_Workspace_runFetchM___rarg___lambda__1(x_1, x_2, x_3, x_12, x_5, x_13, x_14, x_15, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_1, x_2, x_3, x_10, x_5, x_11, x_12, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Workspace_runFetchM___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Workspace_runFetchM___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lake_Workspace_runFetchM___rarg___lambda__5(x_1, x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_9, x_10);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___rarg(x_1, x_2, x_3, x_4);
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
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
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Workspace_runBuild___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___rarg(x_3, x_1, x_2, x_4);
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
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
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_runBuild___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Index(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lock(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkBuildContext___closed__1 = _init_l_Lake_mkBuildContext___closed__1();
lean_mark_persistent(l_Lake_mkBuildContext___closed__1);
l_Lake_mkBuildContext___closed__2 = _init_l_Lake_mkBuildContext___closed__2();
lean_mark_persistent(l_Lake_mkBuildContext___closed__2);
l_Lake_mkBuildContext___closed__3 = _init_l_Lake_mkBuildContext___closed__3();
lean_mark_persistent(l_Lake_mkBuildContext___closed__3);
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
l_Lake_Monitor_spinnerFrames___closed__9 = _init_l_Lake_Monitor_spinnerFrames___closed__9();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames___closed__9);
l_Lake_Monitor_spinnerFrames = _init_l_Lake_Monitor_spinnerFrames();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames);
l_Lake_Ansi_resetLine___closed__1 = _init_l_Lake_Ansi_resetLine___closed__1();
lean_mark_persistent(l_Lake_Ansi_resetLine___closed__1);
l_Lake_Ansi_resetLine = _init_l_Lake_Ansi_resetLine();
lean_mark_persistent(l_Lake_Ansi_resetLine);
l_panic___at_Lake_print_x21___spec__1___closed__1 = _init_l_panic___at_Lake_print_x21___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lake_print_x21___spec__1___closed__1);
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
l_Lake_print_x21___closed__10 = _init_l_Lake_print_x21___closed__10();
lean_mark_persistent(l_Lake_print_x21___closed__10);
l_Lake_print_x21___closed__11 = _init_l_Lake_print_x21___closed__11();
lean_mark_persistent(l_Lake_print_x21___closed__11);
l_Lake_print_x21___closed__12 = _init_l_Lake_print_x21___closed__12();
lean_mark_persistent(l_Lake_print_x21___closed__12);
l_Lake_print_x21___closed__13 = _init_l_Lake_print_x21___closed__13();
lean_mark_persistent(l_Lake_print_x21___closed__13);
l_Lake_Monitor_renderProgress___closed__1 = _init_l_Lake_Monitor_renderProgress___closed__1();
lean_mark_persistent(l_Lake_Monitor_renderProgress___closed__1);
l_Lake_Monitor_renderProgress___closed__2 = _init_l_Lake_Monitor_renderProgress___closed__2();
lean_mark_persistent(l_Lake_Monitor_renderProgress___closed__2);
l_Lake_Monitor_renderProgress___closed__3 = _init_l_Lake_Monitor_renderProgress___closed__3();
lean_mark_persistent(l_Lake_Monitor_renderProgress___closed__3);
l_Lake_Monitor_renderProgress___closed__4 = _init_l_Lake_Monitor_renderProgress___closed__4();
lean_mark_persistent(l_Lake_Monitor_renderProgress___closed__4);
l_Lake_Monitor_renderProgress___closed__5 = _init_l_Lake_Monitor_renderProgress___closed__5();
lean_mark_persistent(l_Lake_Monitor_renderProgress___closed__5);
l_Lake_Monitor_renderProgress___closed__6 = _init_l_Lake_Monitor_renderProgress___closed__6();
lean_mark_persistent(l_Lake_Monitor_renderProgress___closed__6);
l_Lake_Monitor_reportJob___lambda__2___closed__1 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Monitor_reportJob___lambda__2___closed__1);
l_Lake_Monitor_reportJob___lambda__2___closed__2 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Monitor_reportJob___lambda__2___closed__2);
l_Lake_Monitor_reportJob___lambda__2___closed__3 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Monitor_reportJob___lambda__2___closed__3);
l_Lake_Monitor_reportJob___lambda__2___closed__4 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__4();
lean_mark_persistent(l_Lake_Monitor_reportJob___lambda__2___closed__4);
l_Lake_Monitor_reportJob___lambda__2___closed__5 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__5();
lean_mark_persistent(l_Lake_Monitor_reportJob___lambda__2___closed__5);
l_Lake_Monitor_reportJob___lambda__2___closed__6 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__6();
lean_mark_persistent(l_Lake_Monitor_reportJob___lambda__2___closed__6);
l_Lake_Monitor_reportJob___lambda__2___closed__7 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__7();
l_Lake_Monitor_reportJob___lambda__2___closed__8 = _init_l_Lake_Monitor_reportJob___lambda__2___closed__8();
l_Lake_Monitor_poll___closed__1 = _init_l_Lake_Monitor_poll___closed__1();
lean_mark_persistent(l_Lake_Monitor_poll___closed__1);
l_Lake_Monitor_sleep___closed__1 = _init_l_Lake_Monitor_sleep___closed__1();
lean_mark_persistent(l_Lake_Monitor_sleep___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__1___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__3___rarg___closed__5);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__2);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__3);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__4 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__4);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__5 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__5);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__6 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__6();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__6);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__7 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__7();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__7);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__8 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__8();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__8);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__9);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__10 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__10();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__10);
l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__11 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__11();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__1___closed__11);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__2);
l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__2___closed__3);
l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__4___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__2);
l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__3 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__3);
l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__4 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__4();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__4);
l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__5 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__5();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__5___closed__5);
l_Lake_Workspace_runFetchM___rarg___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__1);
l_Lake_Workspace_runFetchM___rarg___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__2);
l_Lake_Workspace_runFetchM___rarg___closed__3 = _init_l_Lake_Workspace_runFetchM___rarg___closed__3();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__3);
l_Lake_Workspace_runFetchM___rarg___closed__4 = _init_l_Lake_Workspace_runFetchM___rarg___closed__4();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__4);
l_Lake_Workspace_runFetchM___rarg___closed__5 = _init_l_Lake_Workspace_runFetchM___rarg___closed__5();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__5);
l_Lake_Workspace_runFetchM___rarg___closed__6 = _init_l_Lake_Workspace_runFetchM___rarg___closed__6();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
