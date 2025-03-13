// Lean compiler output
// Module: Lake.Build.Run
// Imports: Lake.Util.Lock Lake.Build.Index
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lake_Monitor_spinnerFrames___closed__4;
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__1;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__7;
lean_object* l_Lake_recFetchWithIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_print_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__10;
extern lean_object* l_Lake_instOrdJobAction;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__3;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__5;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__6;
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__5;
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__6;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
static lean_object* l_Lake_print_x21___closed__7;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__8;
lean_object* lean_io_mono_ms_now(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__2;
static lean_object* l_Lake_Monitor_renderProgress___closed__2;
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lake_print_x21___closed__8;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__1;
static lean_object* l_Lake_print_x21___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames;
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__3;
static uint8_t l_Lake_Monitor_reportJob___lambda__2___closed__8;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__2;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_print_x21___closed__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
lean_object* l_IO_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__9;
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__4;
extern lean_object* l_Lake_BuildTrace_nil;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__3;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lake_print_x21___closed__5;
static lean_object* l_Lake_mkBuildContext___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Ansi_resetLine___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_sleep___closed__1;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_spinnerFrames___closed__8;
static lean_object* l_Lake_Monitor_renderProgress___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_Monitor_poll___closed__1;
LEAN_EXPORT lean_object* l_Lake_Ansi_resetLine;
static lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__1;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__11;
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__12;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__13;
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_poll(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__4;
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__2;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
static uint8_t l_Lake_Monitor_reportJob___lambda__2___closed__7;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__9;
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_runBuild___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_print_x21___closed__2;
LEAN_EXPORT lean_object* l_Lake_flush(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_print_x21___lambda__1(lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*);
static lean_object* l_Lake_Monitor_renderProgress___closed__6;
static lean_object* l_Lake_Monitor_spinnerFrames___closed__3;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
static lean_object* l_Lake_Monitor_reportJob___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2(lean_object*);
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
x_27 = lean_unsigned_to_nat(77u);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_24);
lean_dec(x_24);
x_30 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_29, x_11);
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
x_32 = lean_unsigned_to_nat(77u);
x_33 = lean_unsigned_to_nat(4u);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_29);
lean_dec(x_29);
x_35 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_34, x_16);
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
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 5);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lake_Monitor_spinnerFrames;
x_22 = lean_array_fget(x_21, x_19);
x_23 = lean_unbox_uint32(x_22);
lean_dec(x_22);
x_24 = l_Lake_Monitor_renderProgress___closed__1;
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Fin_add(x_24, x_19, x_25);
lean_dec(x_19);
x_27 = l_Lake_Ansi_resetLine;
lean_inc(x_17);
lean_inc(x_16);
lean_ctor_set(x_5, 5, x_26);
lean_ctor_set(x_5, 3, x_27);
x_28 = lean_array_get_size(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
x_31 = l_Lake_print_x21___closed__11;
x_32 = lean_string_append(x_31, x_18);
lean_dec(x_18);
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
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = l_Lake_print_x21___closed__10;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_ctor_get(x_20, 4);
lean_inc(x_46);
if (x_30 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_28);
x_153 = lean_array_get_size(x_2);
x_154 = lean_nat_sub(x_153, x_25);
lean_dec(x_153);
x_155 = lean_array_fget(x_2, x_154);
lean_dec(x_154);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lake_Monitor_renderProgress___closed__4;
x_158 = lean_string_append(x_157, x_156);
lean_dec(x_156);
x_159 = lean_string_append(x_158, x_31);
x_47 = x_159;
goto block_152;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_160 = lean_nat_sub(x_28, x_25);
lean_dec(x_28);
x_161 = lean_array_fget(x_1, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lake_Monitor_renderProgress___closed__4;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Lake_Monitor_renderProgress___closed__5;
x_166 = lean_string_append(x_164, x_165);
x_167 = l___private_Init_Data_Repr_0__Nat_reprFast(x_160);
x_168 = lean_string_append(x_166, x_167);
lean_dec(x_167);
x_169 = l_Lake_Monitor_renderProgress___closed__6;
x_170 = lean_string_append(x_168, x_169);
x_47 = x_170;
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
x_95 = lean_unsigned_to_nat(77u);
x_96 = lean_unsigned_to_nat(4u);
x_97 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_93, x_94, x_95, x_96, x_92);
lean_dec(x_92);
x_98 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_97, x_82);
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
x_131 = lean_unsigned_to_nat(77u);
x_132 = lean_unsigned_to_nat(4u);
x_133 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_129, x_130, x_131, x_132, x_128);
lean_dec(x_128);
x_134 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_133, x_118);
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
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint32_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_171 = lean_ctor_get(x_5, 0);
x_172 = lean_ctor_get(x_5, 1);
x_173 = lean_ctor_get(x_5, 2);
x_174 = lean_ctor_get(x_5, 3);
x_175 = lean_ctor_get(x_5, 4);
x_176 = lean_ctor_get(x_5, 5);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_5);
x_177 = lean_ctor_get(x_4, 1);
lean_inc(x_177);
lean_dec(x_4);
x_178 = l_Lake_Monitor_spinnerFrames;
x_179 = lean_array_fget(x_178, x_176);
x_180 = lean_unbox_uint32(x_179);
lean_dec(x_179);
x_181 = l_Lake_Monitor_renderProgress___closed__1;
x_182 = lean_unsigned_to_nat(1u);
x_183 = l_Fin_add(x_181, x_176, x_182);
lean_dec(x_176);
x_184 = l_Lake_Ansi_resetLine;
lean_inc(x_172);
lean_inc(x_171);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_171);
lean_ctor_set(x_185, 1, x_172);
lean_ctor_set(x_185, 2, x_173);
lean_ctor_set(x_185, 3, x_184);
lean_ctor_set(x_185, 4, x_175);
lean_ctor_set(x_185, 5, x_183);
x_186 = lean_array_get_size(x_1);
x_187 = lean_unsigned_to_nat(0u);
x_188 = lean_nat_dec_lt(x_187, x_186);
x_189 = l_Lake_print_x21___closed__11;
x_190 = lean_string_append(x_189, x_174);
lean_dec(x_174);
x_191 = lean_string_append(x_190, x_189);
x_192 = lean_string_push(x_189, x_180);
x_193 = lean_string_append(x_191, x_192);
lean_dec(x_192);
x_194 = l_Lake_Monitor_renderProgress___closed__2;
x_195 = lean_string_append(x_193, x_194);
x_196 = l___private_Init_Data_Repr_0__Nat_reprFast(x_171);
x_197 = lean_string_append(x_195, x_196);
lean_dec(x_196);
x_198 = l_Lake_Monitor_renderProgress___closed__3;
x_199 = lean_string_append(x_197, x_198);
x_200 = l___private_Init_Data_Repr_0__Nat_reprFast(x_172);
x_201 = lean_string_append(x_199, x_200);
lean_dec(x_200);
x_202 = l_Lake_print_x21___closed__10;
x_203 = lean_string_append(x_201, x_202);
x_204 = lean_ctor_get(x_177, 4);
lean_inc(x_204);
if (x_188 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_186);
x_260 = lean_array_get_size(x_2);
x_261 = lean_nat_sub(x_260, x_182);
lean_dec(x_260);
x_262 = lean_array_fget(x_2, x_261);
lean_dec(x_261);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Lake_Monitor_renderProgress___closed__4;
x_265 = lean_string_append(x_264, x_263);
lean_dec(x_263);
x_266 = lean_string_append(x_265, x_189);
x_205 = x_266;
goto block_259;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_267 = lean_nat_sub(x_186, x_182);
lean_dec(x_186);
x_268 = lean_array_fget(x_1, x_267);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = l_Lake_Monitor_renderProgress___closed__4;
x_271 = lean_string_append(x_270, x_269);
lean_dec(x_269);
x_272 = l_Lake_Monitor_renderProgress___closed__5;
x_273 = lean_string_append(x_271, x_272);
x_274 = l___private_Init_Data_Repr_0__Nat_reprFast(x_267);
x_275 = lean_string_append(x_273, x_274);
lean_dec(x_274);
x_276 = l_Lake_Monitor_renderProgress___closed__6;
x_277 = lean_string_append(x_275, x_276);
x_205 = x_277;
goto block_259;
}
block_259:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_string_append(x_203, x_205);
lean_dec(x_205);
x_207 = lean_string_append(x_206, x_189);
lean_inc(x_207);
x_208 = lean_apply_2(x_204, x_207, x_6);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_177, 0);
lean_inc(x_211);
lean_dec(x_177);
x_212 = lean_apply_1(x_211, x_209);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_185);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_214);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_219 = x_212;
} else {
 lean_dec_ref(x_212);
 x_219 = lean_box(0);
}
x_220 = lean_box(0);
if (lean_is_scalar(x_210)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_210;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_185);
if (lean_is_scalar(x_219)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_219;
 lean_ctor_set_tag(x_222, 0);
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_223 = lean_ctor_get(x_208, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_208, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_225 = x_208;
} else {
 lean_dec_ref(x_208);
 x_225 = lean_box(0);
}
x_226 = lean_io_error_to_string(x_223);
x_227 = l_Lake_print_x21___closed__9;
x_228 = lean_string_append(x_227, x_226);
lean_dec(x_226);
x_229 = lean_string_append(x_228, x_202);
x_230 = l_String_quote(x_207);
lean_dec(x_207);
x_231 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = l_Std_Format_defWidth;
x_233 = lean_format_pretty(x_231, x_232, x_187, x_187);
x_234 = lean_string_append(x_229, x_233);
lean_dec(x_233);
x_235 = lean_string_append(x_234, x_189);
x_236 = l_Lake_print_x21___closed__12;
x_237 = l_Lake_print_x21___closed__13;
x_238 = lean_unsigned_to_nat(77u);
x_239 = lean_unsigned_to_nat(4u);
x_240 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_236, x_237, x_238, x_239, x_235);
lean_dec(x_235);
x_241 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_240, x_224);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_ctor_get(x_177, 0);
lean_inc(x_243);
lean_dec(x_177);
x_244 = lean_apply_1(x_243, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
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
if (lean_is_scalar(x_225)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_225;
 lean_ctor_set_tag(x_248, 0);
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_185);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_246);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
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
x_252 = lean_box(0);
if (lean_is_scalar(x_225)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_225;
 lean_ctor_set_tag(x_253, 0);
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_185);
if (lean_is_scalar(x_251)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_251;
 lean_ctor_set_tag(x_254, 0);
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_225);
lean_dec(x_185);
lean_dec(x_177);
x_255 = lean_ctor_get(x_241, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_241, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_257 = x_241;
} else {
 lean_dec_ref(x_241);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
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
uint8_t x_332; 
x_332 = 0;
x_19 = x_332;
goto block_331;
}
else
{
uint8_t x_333; 
x_333 = 1;
x_19 = x_333;
goto block_331;
}
block_331:
{
lean_object* x_20; lean_object* x_279; lean_object* x_308; uint8_t x_325; 
x_325 = l_instDecidableNot___rarg(x_19);
if (x_325 == 0)
{
if (x_13 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_326 = lean_box(0);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_17);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_18);
return x_328;
}
else
{
lean_object* x_329; 
x_329 = lean_box(0);
x_308 = x_329;
goto block_324;
}
}
else
{
lean_object* x_330; 
x_330 = lean_box(0);
x_308 = x_330;
goto block_324;
}
block_278:
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
uint8_t x_276; 
x_276 = 0;
x_27 = x_276;
goto block_275;
}
else
{
uint8_t x_277; 
x_277 = 1;
x_27 = x_277;
goto block_275;
}
block_275:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_268; 
x_268 = 0;
x_28 = x_268;
goto block_267;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = l_Lake_instOrdLogLevel;
x_270 = lean_box(x_10);
x_271 = lean_box(x_9);
x_272 = l_Ord_instDecidableRelLe___rarg(x_269, x_270, x_271);
if (x_272 == 0)
{
uint8_t x_273; 
x_273 = 0;
x_28 = x_273;
goto block_267;
}
else
{
uint8_t x_274; 
x_274 = 1;
x_28 = x_274;
goto block_267;
}
}
block_267:
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lake_JobAction_verb(x_28, x_4);
if (x_28 == 0)
{
if (x_27 == 0)
{
uint8_t x_259; 
x_259 = 0;
x_30 = x_259;
goto block_258;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = l_Lake_instOrdLogLevel;
x_261 = lean_box(x_6);
x_262 = lean_box(x_9);
x_263 = l_Ord_instDecidableRelLe___rarg(x_260, x_261, x_262);
if (x_263 == 0)
{
uint8_t x_264; 
x_264 = 0;
x_30 = x_264;
goto block_258;
}
else
{
uint8_t x_265; 
x_265 = 1;
x_30 = x_265;
goto block_258;
}
}
}
else
{
uint8_t x_266; 
x_266 = 1;
x_30 = x_266;
goto block_258;
}
block_258:
{
lean_object* x_31; uint32_t x_220; 
if (x_30 == 0)
{
uint32_t x_256; 
x_256 = 10004;
x_220 = x_256;
goto block_255;
}
else
{
uint32_t x_257; 
x_257 = l_Lake_LogLevel_icon(x_9);
x_220 = x_257;
goto block_255;
}
block_219:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_33 = lean_ctor_get(x_17, 3);
x_34 = l_Lake_print_x21___closed__11;
lean_ctor_set(x_17, 3, x_34);
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
x_100 = lean_unsigned_to_nat(77u);
x_101 = lean_unsigned_to_nat(4u);
x_102 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_98, x_99, x_100, x_101, x_97);
lean_dec(x_97);
x_103 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_102, x_86);
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
x_125 = lean_unsigned_to_nat(77u);
x_126 = lean_unsigned_to_nat(4u);
x_127 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_123, x_124, x_125, x_126, x_122);
lean_dec(x_122);
x_128 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_127, x_111);
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
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_136 = lean_ctor_get(x_17, 0);
x_137 = lean_ctor_get(x_17, 1);
x_138 = lean_ctor_get(x_17, 2);
x_139 = lean_ctor_get(x_17, 3);
x_140 = lean_ctor_get(x_17, 4);
x_141 = lean_ctor_get(x_17, 5);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_17);
x_142 = l_Lake_print_x21___closed__11;
x_143 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_137);
lean_ctor_set(x_143, 2, x_138);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_143, 4, x_140);
lean_ctor_set(x_143, 5, x_141);
x_180 = lean_string_append(x_142, x_139);
lean_dec(x_139);
x_181 = lean_string_append(x_180, x_142);
x_182 = lean_string_append(x_181, x_31);
lean_dec(x_31);
x_183 = l_Lake_Monitor_reportJob___lambda__2___closed__2;
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_ctor_get(x_16, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 4);
lean_inc(x_186);
lean_dec(x_185);
lean_inc(x_184);
x_187 = lean_apply_2(x_186, x_184, x_18);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_143);
x_144 = x_191;
x_145 = x_189;
goto block_179;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_192 = lean_ctor_get(x_187, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_194 = x_187;
} else {
 lean_dec_ref(x_187);
 x_194 = lean_box(0);
}
x_195 = lean_io_error_to_string(x_192);
x_196 = l_Lake_print_x21___closed__9;
x_197 = lean_string_append(x_196, x_195);
lean_dec(x_195);
x_198 = l_Lake_print_x21___closed__10;
x_199 = lean_string_append(x_197, x_198);
x_200 = l_String_quote(x_184);
lean_dec(x_184);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Std_Format_defWidth;
x_203 = lean_format_pretty(x_201, x_202, x_22, x_22);
x_204 = lean_string_append(x_199, x_203);
lean_dec(x_203);
x_205 = lean_string_append(x_204, x_142);
x_206 = l_Lake_print_x21___closed__12;
x_207 = l_Lake_print_x21___closed__13;
x_208 = lean_unsigned_to_nat(77u);
x_209 = lean_unsigned_to_nat(4u);
x_210 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_206, x_207, x_208, x_209, x_205);
lean_dec(x_205);
x_211 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_210, x_193);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
if (lean_is_scalar(x_194)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_194;
 lean_ctor_set_tag(x_214, 0);
}
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_143);
x_144 = x_214;
x_145 = x_213;
goto block_179;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_194);
lean_dec(x_143);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_5);
x_215 = lean_ctor_get(x_211, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_211, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_217 = x_211;
} else {
 lean_dec_ref(x_211);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
block_179:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lake_Monitor_reportJob___lambda__2___closed__1;
if (x_30 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_21);
lean_dec(x_5);
x_148 = lean_box(0);
x_149 = lean_apply_4(x_147, x_148, x_16, x_146, x_145);
return x_149;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_lt(x_22, x_21);
if (x_28 == 0)
{
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_21);
lean_dec(x_5);
x_151 = lean_box(0);
x_152 = lean_apply_4(x_147, x_151, x_16, x_146, x_145);
return x_152;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_21, x_21);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_21);
lean_dec(x_5);
x_154 = lean_box(0);
x_155 = lean_apply_4(x_147, x_154, x_16, x_146, x_145);
return x_155;
}
else
{
size_t x_156; size_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_156 = 0;
x_157 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_158 = lean_box(0);
x_159 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__1(x_5, x_6, x_7, x_1, x_156, x_157, x_158, x_16, x_146, x_145);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_apply_4(x_147, x_162, x_16, x_163, x_161);
return x_164;
}
}
}
else
{
if (x_150 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_21);
lean_dec(x_5);
x_165 = lean_box(0);
x_166 = lean_apply_4(x_147, x_165, x_16, x_146, x_145);
return x_166;
}
else
{
uint8_t x_167; 
x_167 = lean_nat_dec_le(x_21, x_21);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_21);
lean_dec(x_5);
x_168 = lean_box(0);
x_169 = lean_apply_4(x_147, x_168, x_16, x_146, x_145);
return x_169;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_170 = 0;
x_171 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_172 = lean_box(0);
x_173 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_reportJob___spec__2(x_5, x_7, x_1, x_170, x_171, x_172, x_16, x_146, x_145);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_apply_4(x_147, x_176, x_16, x_177, x_175);
return x_178;
}
}
}
}
}
}
}
block_255:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_221 = l_Lake_print_x21___closed__11;
x_222 = lean_string_push(x_221, x_220);
x_223 = lean_string_append(x_221, x_222);
lean_dec(x_222);
x_224 = l_Lake_Monitor_renderProgress___closed__2;
x_225 = lean_string_append(x_223, x_224);
x_226 = lean_string_append(x_225, x_25);
lean_dec(x_25);
x_227 = l_Lake_Monitor_renderProgress___closed__3;
x_228 = lean_string_append(x_226, x_227);
x_229 = lean_string_append(x_228, x_26);
lean_dec(x_26);
x_230 = l_Lake_Monitor_reportJob___lambda__2___closed__3;
x_231 = lean_string_append(x_229, x_230);
if (x_19 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_232 = lean_string_append(x_231, x_221);
x_233 = l_Lake_Monitor_reportJob___lambda__2___closed__4;
x_234 = lean_string_append(x_232, x_233);
x_235 = lean_string_append(x_234, x_29);
lean_dec(x_29);
x_236 = lean_string_append(x_235, x_233);
x_237 = lean_string_append(x_236, x_8);
x_238 = lean_string_append(x_237, x_221);
if (x_7 == 0)
{
x_31 = x_238;
goto block_219;
}
else
{
if (x_30 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = l_Lake_Monitor_reportJob___lambda__2___closed__5;
x_240 = l_Lake_Ansi_chalk(x_239, x_238);
lean_dec(x_238);
x_31 = x_240;
goto block_219;
}
else
{
lean_object* x_241; lean_object* x_242; 
x_241 = l_Lake_LogLevel_ansiColor(x_9);
x_242 = l_Lake_Ansi_chalk(x_241, x_238);
lean_dec(x_238);
lean_dec(x_241);
x_31 = x_242;
goto block_219;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = l_Lake_Monitor_reportJob___lambda__2___closed__6;
x_244 = lean_string_append(x_231, x_243);
x_245 = l_Lake_Monitor_reportJob___lambda__2___closed__4;
x_246 = lean_string_append(x_244, x_245);
x_247 = lean_string_append(x_246, x_29);
lean_dec(x_29);
x_248 = lean_string_append(x_247, x_245);
x_249 = lean_string_append(x_248, x_8);
x_250 = lean_string_append(x_249, x_221);
if (x_7 == 0)
{
x_31 = x_250;
goto block_219;
}
else
{
if (x_30 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = l_Lake_Monitor_reportJob___lambda__2___closed__5;
x_252 = l_Lake_Ansi_chalk(x_251, x_250);
lean_dec(x_250);
x_31 = x_252;
goto block_219;
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = l_Lake_LogLevel_ansiColor(x_9);
x_254 = l_Lake_Ansi_chalk(x_253, x_250);
lean_dec(x_250);
lean_dec(x_253);
x_31 = x_254;
goto block_219;
}
}
}
}
}
}
}
}
block_307:
{
lean_dec(x_279);
if (x_11 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_17);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_18);
return x_282;
}
else
{
if (x_7 == 0)
{
uint8_t x_283; 
x_283 = l_Lake_Monitor_reportJob___lambda__2___closed__7;
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_284 = lean_box(0);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_17);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_18);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_287 = l_Lake_instOrdJobAction;
x_288 = lean_box(x_12);
x_289 = lean_box(x_4);
x_290 = l_Ord_instDecidableRelLe___rarg(x_287, x_288, x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_291 = lean_box(0);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_17);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_18);
return x_293;
}
else
{
lean_object* x_294; 
x_294 = lean_box(0);
x_20 = x_294;
goto block_278;
}
}
}
else
{
uint8_t x_295; 
x_295 = l_Lake_Monitor_reportJob___lambda__2___closed__8;
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_296 = lean_box(0);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_17);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_18);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_299 = l_Lake_instOrdJobAction;
x_300 = lean_box(x_12);
x_301 = lean_box(x_4);
x_302 = l_Ord_instDecidableRelLe___rarg(x_299, x_300, x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_303 = lean_box(0);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_17);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_18);
return x_305;
}
else
{
lean_object* x_306; 
x_306 = lean_box(0);
x_20 = x_306;
goto block_278;
}
}
}
}
}
block_324:
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; uint8_t x_312; 
lean_dec(x_308);
x_309 = lean_array_get_size(x_1);
x_310 = lean_unsigned_to_nat(0u);
x_311 = lean_nat_dec_eq(x_309, x_310);
lean_dec(x_309);
x_312 = l_instDecidableNot___rarg(x_311);
if (x_312 == 0)
{
lean_object* x_313; 
x_313 = lean_box(0);
x_279 = x_313;
goto block_307;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = l_Lake_instOrdLogLevel;
x_315 = lean_box(x_10);
x_316 = lean_box(x_9);
x_317 = l_Ord_instDecidableRelLe___rarg(x_314, x_315, x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_318 = lean_box(x_6);
x_319 = lean_box(x_9);
x_320 = l_Ord_instDecidableRelLe___rarg(x_314, x_318, x_319);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_box(0);
x_279 = x_321;
goto block_307;
}
else
{
lean_object* x_322; 
x_322 = lean_box(0);
x_20 = x_322;
goto block_278;
}
}
else
{
lean_object* x_323; 
x_323 = lean_box(0);
x_20 = x_323;
goto block_278;
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
x_10 = lean_ctor_get(x_3, 5);
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
x_54 = lean_ctor_get_uint8(x_52, sizeof(void*)*2);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_34 = lean_box(0);
x_35 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_6, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_34, x_2, x_3, x_4);
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
x_39 = l_Ord_instDecidableRelLe___rarg(x_36, x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = lean_box(0);
x_41 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_6, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_40, x_2, x_3, x_4);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_43 = lean_box(0);
x_44 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_6, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_43, x_2, x_3, x_4);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_47 = lean_box(0);
x_48 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_6, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_47, x_2, x_3, x_4);
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
x_25 = lean_array_push(x_7, x_19);
lean_inc(x_6);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_8);
lean_ctor_set(x_26, 4, x_9);
lean_ctor_set(x_26, 5, x_10);
x_27 = lean_box(0);
x_28 = l_Lake_Monitor_reportJob___lambda__2(x_21, x_5, x_6, x_22, x_11, x_12, x_16, x_19, x_23, x_13, x_17, x_14, x_15, x_20, x_27, x_2, x_26, x_4);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
x_44 = lean_ctor_get(x_32, 2);
x_45 = lean_ctor_get(x_32, 3);
x_46 = lean_ctor_get(x_32, 4);
x_47 = lean_ctor_get(x_32, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_42, x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 0, x_11);
x_51 = 1;
x_52 = lean_usize_add(x_2, x_51);
x_2 = x_52;
x_4 = x_30;
x_6 = x_50;
x_7 = x_34;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_dec(x_29);
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
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_56, x_63);
lean_dec(x_56);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 6, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_59);
lean_ctor_set(x_65, 4, x_60);
lean_ctor_set(x_65, 5, x_61);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_11);
lean_ctor_set(x_66, 1, x_12);
x_67 = 1;
x_68 = lean_usize_add(x_2, x_67);
x_2 = x_68;
x_4 = x_66;
x_6 = x_65;
x_7 = x_55;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_14);
if (x_74 == 0)
{
return x_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_4, 0);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_4);
x_80 = lean_ctor_get(x_9, 0);
lean_inc(x_80);
x_81 = lean_io_get_task_state(x_80, x_7);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
switch (x_83) {
case 0:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_array_push(x_79, x_9);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_85);
x_87 = 1;
x_88 = lean_usize_add(x_2, x_87);
x_2 = x_88;
x_4 = x_86;
x_7 = x_84;
goto _start;
}
case 1:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
lean_inc(x_9);
x_91 = lean_array_push(x_78, x_9);
x_92 = lean_array_push(x_79, x_9);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = 1;
x_95 = lean_usize_add(x_2, x_94);
x_2 = x_95;
x_4 = x_93;
x_7 = x_90;
goto _start;
}
default: 
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_dec(x_81);
lean_inc(x_5);
x_98 = l_Lake_Monitor_reportJob(x_9, x_5, x_6, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
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
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_100, 5);
lean_inc(x_108);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 x_109 = x_100;
} else {
 lean_dec_ref(x_100);
 x_109 = lean_box(0);
}
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_103, x_110);
lean_dec(x_103);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 6, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_107);
lean_ctor_set(x_112, 5, x_108);
if (lean_is_scalar(x_101)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_101;
}
lean_ctor_set(x_113, 0, x_78);
lean_ctor_set(x_113, 1, x_79);
x_114 = 1;
x_115 = lean_usize_add(x_2, x_114);
x_2 = x_115;
x_4 = x_113;
x_6 = x_112;
x_7 = x_102;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_5);
x_117 = lean_ctor_get(x_98, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_98, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_119 = x_98;
} else {
 lean_dec_ref(x_98);
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
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_ctor_get(x_81, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_81, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_123 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_5);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_4);
lean_ctor_set(x_125, 1, x_6);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_7);
return x_126;
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
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_st_ref_take(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lake_mkBuildContext___closed__1;
x_10 = lean_st_ref_set(x_5, x_9, x_8);
lean_dec(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_15);
lean_ctor_set(x_3, 1, x_17);
x_18 = lean_array_get_size(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = lean_nat_dec_lt(x_19, x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_22 = l_Lake_Monitor_poll___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_16, x_16);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_25 = l_Lake_Monitor_poll___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_10);
x_27 = 0;
x_28 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_29 = l_Lake_Monitor_poll___closed__1;
x_30 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_27, x_28, x_29, x_2, x_3, x_12);
lean_dec(x_7);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_18, x_18);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_18);
x_32 = lean_nat_dec_lt(x_19, x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_33 = l_Lake_Monitor_poll___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_10, 0, x_34);
return x_10;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_16, x_16);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_36 = l_Lake_Monitor_poll___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_10, 0, x_37);
return x_10;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_10);
x_38 = 0;
x_39 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_40 = l_Lake_Monitor_poll___closed__1;
x_41 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_38, x_39, x_40, x_2, x_3, x_12);
lean_dec(x_7);
return x_41;
}
}
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_10);
x_42 = 0;
x_43 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_44 = l_Lake_Monitor_poll___closed__1;
lean_inc(x_2);
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_1, x_42, x_43, x_44, x_2, x_3, x_12);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 1);
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
x_52 = lean_nat_dec_lt(x_19, x_16);
if (x_52 == 0)
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
return x_45;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_16, x_16);
if (x_53 == 0)
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
return x_45;
}
else
{
size_t x_54; lean_object* x_55; 
lean_free_object(x_47);
lean_free_object(x_45);
x_54 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_55 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_42, x_54, x_50, x_2, x_51, x_49);
lean_dec(x_7);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_45, 1);
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_nat_dec_lt(x_19, x_16);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_45, 0, x_60);
return x_45;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_16, x_16);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set(x_45, 0, x_62);
return x_45;
}
else
{
size_t x_63; lean_object* x_64; 
lean_free_object(x_45);
x_63 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_64 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_42, x_63, x_57, x_2, x_58, x_56);
lean_dec(x_7);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_nat_dec_lt(x_19, x_16);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_16, x_16);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_68);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
else
{
size_t x_76; lean_object* x_77; 
lean_dec(x_69);
x_76 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_77 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_42, x_76, x_67, x_2, x_68, x_66);
lean_dec(x_7);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_45);
if (x_78 == 0)
{
return x_45;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_45, 0);
x_80 = lean_ctor_get(x_45, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_45);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_82 = lean_ctor_get(x_3, 0);
x_83 = lean_ctor_get(x_3, 1);
x_84 = lean_ctor_get(x_3, 2);
x_85 = lean_ctor_get(x_3, 3);
x_86 = lean_ctor_get(x_3, 4);
x_87 = lean_ctor_get(x_3, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_3);
x_88 = lean_array_get_size(x_7);
x_89 = lean_nat_add(x_83, x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_84);
lean_ctor_set(x_90, 3, x_85);
lean_ctor_set(x_90, 4, x_86);
lean_ctor_set(x_90, 5, x_87);
x_91 = lean_array_get_size(x_1);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_lt(x_92, x_91);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_91);
x_94 = lean_nat_dec_lt(x_92, x_88);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
x_95 = l_Lake_Monitor_poll___closed__1;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_10, 0, x_96);
return x_10;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_88, x_88);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
x_98 = l_Lake_Monitor_poll___closed__1;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_90);
lean_ctor_set(x_10, 0, x_99);
return x_10;
}
else
{
size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_10);
x_100 = 0;
x_101 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_102 = l_Lake_Monitor_poll___closed__1;
x_103 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_100, x_101, x_102, x_2, x_90, x_12);
lean_dec(x_7);
return x_103;
}
}
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_91, x_91);
if (x_104 == 0)
{
uint8_t x_105; 
lean_dec(x_91);
x_105 = lean_nat_dec_lt(x_92, x_88);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
x_106 = l_Lake_Monitor_poll___closed__1;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_90);
lean_ctor_set(x_10, 0, x_107);
return x_10;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_88, x_88);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
x_109 = l_Lake_Monitor_poll___closed__1;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_10, 0, x_110);
return x_10;
}
else
{
size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_10);
x_111 = 0;
x_112 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_113 = l_Lake_Monitor_poll___closed__1;
x_114 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_111, x_112, x_113, x_2, x_90, x_12);
lean_dec(x_7);
return x_114;
}
}
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_10);
x_115 = 0;
x_116 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_117 = l_Lake_Monitor_poll___closed__1;
lean_inc(x_2);
x_118 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_1, x_115, x_116, x_117, x_2, x_90, x_12);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_nat_dec_lt(x_92, x_88);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_123);
if (lean_is_scalar(x_121)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_121;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
return x_127;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_88, x_88);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_123);
if (lean_is_scalar(x_121)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_121;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_120);
return x_130;
}
else
{
size_t x_131; lean_object* x_132; 
lean_dec(x_124);
lean_dec(x_121);
x_131 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_132 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_115, x_131, x_122, x_2, x_123, x_120);
lean_dec(x_7);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_88);
lean_dec(x_7);
lean_dec(x_2);
x_133 = lean_ctor_get(x_118, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_118, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_135 = x_118;
} else {
 lean_dec_ref(x_118);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_137 = lean_ctor_get(x_10, 1);
lean_inc(x_137);
lean_dec(x_10);
x_138 = lean_ctor_get(x_3, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_3, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_3, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_3, 5);
lean_inc(x_143);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_144 = x_3;
} else {
 lean_dec_ref(x_3);
 x_144 = lean_box(0);
}
x_145 = lean_array_get_size(x_7);
x_146 = lean_nat_add(x_139, x_145);
lean_dec(x_139);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 6, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_138);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_140);
lean_ctor_set(x_147, 3, x_141);
lean_ctor_set(x_147, 4, x_142);
lean_ctor_set(x_147, 5, x_143);
x_148 = lean_array_get_size(x_1);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_lt(x_149, x_148);
if (x_150 == 0)
{
uint8_t x_151; 
lean_dec(x_148);
x_151 = lean_nat_dec_lt(x_149, x_145);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
x_152 = l_Lake_Monitor_poll___closed__1;
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_137);
return x_154;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_145, x_145);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
x_156 = l_Lake_Monitor_poll___closed__1;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_147);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_137);
return x_158;
}
else
{
size_t x_159; size_t x_160; lean_object* x_161; lean_object* x_162; 
x_159 = 0;
x_160 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_161 = l_Lake_Monitor_poll___closed__1;
x_162 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_159, x_160, x_161, x_2, x_147, x_137);
lean_dec(x_7);
return x_162;
}
}
}
else
{
uint8_t x_163; 
x_163 = lean_nat_dec_le(x_148, x_148);
if (x_163 == 0)
{
uint8_t x_164; 
lean_dec(x_148);
x_164 = lean_nat_dec_lt(x_149, x_145);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
x_165 = l_Lake_Monitor_poll___closed__1;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_147);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_137);
return x_167;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_145, x_145);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
x_169 = l_Lake_Monitor_poll___closed__1;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_147);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_137);
return x_171;
}
else
{
size_t x_172; size_t x_173; lean_object* x_174; lean_object* x_175; 
x_172 = 0;
x_173 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_174 = l_Lake_Monitor_poll___closed__1;
x_175 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_172, x_173, x_174, x_2, x_147, x_137);
lean_dec(x_7);
return x_175;
}
}
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; 
x_176 = 0;
x_177 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_178 = l_Lake_Monitor_poll___closed__1;
lean_inc(x_2);
x_179 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_1, x_176, x_177, x_178, x_2, x_147, x_137);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_185 = x_180;
} else {
 lean_dec_ref(x_180);
 x_185 = lean_box(0);
}
x_186 = lean_nat_dec_lt(x_149, x_145);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_182;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
return x_188;
}
else
{
uint8_t x_189; 
x_189 = lean_nat_dec_le(x_145, x_145);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_185)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_185;
}
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_182;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_181);
return x_191;
}
else
{
size_t x_192; lean_object* x_193; 
lean_dec(x_185);
lean_dec(x_182);
x_192 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_193 = l_Array_foldlMUnsafe_fold___at_Lake_Monitor_poll___spec__1(x_7, x_176, x_192, x_183, x_2, x_184, x_181);
lean_dec(x_7);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_2);
x_194 = lean_ctor_get(x_179, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_179, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_196 = x_179;
} else {
 lean_dec_ref(x_179);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_10);
if (x_198 == 0)
{
return x_10;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_10, 0);
x_200 = lean_ctor_get(x_10, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_10);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_202 = !lean_is_exclusive(x_6);
if (x_202 == 0)
{
return x_6;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_6, 0);
x_204 = lean_ctor_get(x_6, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_6);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
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
x_9 = lean_ctor_get(x_3, 4);
lean_dec(x_9);
lean_ctor_set(x_3, 4, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_12);
lean_ctor_set(x_18, 5, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 5);
lean_inc(x_27);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_28 = x_3;
} else {
 lean_dec_ref(x_3);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 6, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_21);
lean_ctor_set(x_29, 5, x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
x_7 = lean_ctor_get(x_2, 4);
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
x_14 = lean_ctor_get(x_8, 3);
x_15 = l_Lake_print_x21___closed__11;
lean_ctor_set(x_8, 3, x_15);
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
x_51 = lean_unsigned_to_nat(77u);
x_52 = lean_unsigned_to_nat(4u);
x_53 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_49, x_50, x_51, x_52, x_48);
lean_dec(x_48);
x_54 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_53, x_37);
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
x_76 = lean_ctor_get(x_8, 2);
x_77 = lean_ctor_get(x_8, 3);
x_78 = lean_ctor_get(x_8, 4);
x_79 = lean_ctor_get(x_8, 5);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_80 = l_Lake_print_x21___closed__11;
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_79);
x_82 = lean_string_utf8_byte_size(x_77);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_nat_dec_eq(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_5);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_ctor_get(x_85, 4);
lean_inc(x_86);
lean_inc(x_77);
x_87 = lean_apply_2(x_86, x_77, x_11);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_77);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_apply_1(x_89, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_81);
lean_ctor_set(x_6, 0, x_91);
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_6);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
x_97 = lean_box(0);
lean_ctor_set(x_6, 1, x_81);
lean_ctor_set(x_6, 0, x_97);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
 lean_ctor_set_tag(x_98, 0);
}
lean_ctor_set(x_98, 0, x_6);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 1);
lean_inc(x_100);
lean_dec(x_87);
x_101 = lean_io_error_to_string(x_99);
x_102 = l_Lake_print_x21___closed__9;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lake_print_x21___closed__10;
x_105 = lean_string_append(x_103, x_104);
x_106 = l_String_quote(x_77);
lean_dec(x_77);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Std_Format_defWidth;
x_109 = lean_format_pretty(x_107, x_108, x_83, x_83);
x_110 = lean_string_append(x_105, x_109);
lean_dec(x_109);
x_111 = lean_string_append(x_110, x_80);
x_112 = l_Lake_print_x21___closed__12;
x_113 = l_Lake_print_x21___closed__13;
x_114 = lean_unsigned_to_nat(77u);
x_115 = lean_unsigned_to_nat(4u);
x_116 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_112, x_113, x_114, x_115, x_111);
lean_dec(x_111);
x_117 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_116, x_100);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_ctor_get(x_85, 0);
lean_inc(x_119);
lean_dec(x_85);
x_120 = lean_apply_1(x_119, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_81);
lean_ctor_set(x_6, 0, x_121);
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_6);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
lean_ctor_set(x_6, 1, x_81);
lean_ctor_set(x_6, 0, x_127);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
 lean_ctor_set_tag(x_128, 0);
}
lean_ctor_set(x_128, 0, x_6);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_85);
lean_dec(x_81);
lean_free_object(x_6);
x_129 = lean_ctor_get(x_117, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_117, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_131 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
else
{
lean_object* x_133; 
lean_dec(x_77);
lean_dec(x_2);
x_133 = lean_box(0);
lean_ctor_set(x_6, 1, x_81);
lean_ctor_set(x_6, 0, x_133);
return x_5;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_134 = lean_ctor_get(x_5, 1);
lean_inc(x_134);
lean_dec(x_5);
x_135 = lean_ctor_get(x_8, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_8, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_8, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_8, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_8, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_8, 5);
lean_inc(x_140);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 x_141 = x_8;
} else {
 lean_dec_ref(x_8);
 x_141 = lean_box(0);
}
x_142 = l_Lake_print_x21___closed__11;
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_136);
lean_ctor_set(x_143, 2, x_137);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_143, 4, x_139);
lean_ctor_set(x_143, 5, x_140);
x_144 = lean_string_utf8_byte_size(x_138);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_nat_dec_eq(x_144, x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_2, 1);
lean_inc(x_147);
lean_dec(x_2);
x_148 = lean_ctor_get(x_147, 4);
lean_inc(x_148);
lean_inc(x_138);
x_149 = lean_apply_2(x_148, x_138, x_134);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_138);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_apply_1(x_151, x_150);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_143);
lean_ctor_set(x_6, 0, x_153);
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_6);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_158 = x_152;
} else {
 lean_dec_ref(x_152);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
lean_ctor_set(x_6, 1, x_143);
lean_ctor_set(x_6, 0, x_159);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
 lean_ctor_set_tag(x_160, 0);
}
lean_ctor_set(x_160, 0, x_6);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_161 = lean_ctor_get(x_149, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_149, 1);
lean_inc(x_162);
lean_dec(x_149);
x_163 = lean_io_error_to_string(x_161);
x_164 = l_Lake_print_x21___closed__9;
x_165 = lean_string_append(x_164, x_163);
lean_dec(x_163);
x_166 = l_Lake_print_x21___closed__10;
x_167 = lean_string_append(x_165, x_166);
x_168 = l_String_quote(x_138);
lean_dec(x_138);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Std_Format_defWidth;
x_171 = lean_format_pretty(x_169, x_170, x_145, x_145);
x_172 = lean_string_append(x_167, x_171);
lean_dec(x_171);
x_173 = lean_string_append(x_172, x_142);
x_174 = l_Lake_print_x21___closed__12;
x_175 = l_Lake_print_x21___closed__13;
x_176 = lean_unsigned_to_nat(77u);
x_177 = lean_unsigned_to_nat(4u);
x_178 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_174, x_175, x_176, x_177, x_173);
lean_dec(x_173);
x_179 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_178, x_162);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_ctor_get(x_147, 0);
lean_inc(x_181);
lean_dec(x_147);
x_182 = lean_apply_1(x_181, x_180);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_143);
lean_ctor_set(x_6, 0, x_183);
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_6);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_188 = x_182;
} else {
 lean_dec_ref(x_182);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
lean_ctor_set(x_6, 1, x_143);
lean_ctor_set(x_6, 0, x_189);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
 lean_ctor_set_tag(x_190, 0);
}
lean_ctor_set(x_190, 0, x_6);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_147);
lean_dec(x_143);
lean_free_object(x_6);
x_191 = lean_ctor_get(x_179, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_179, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_193 = x_179;
} else {
 lean_dec_ref(x_179);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_138);
lean_dec(x_2);
x_195 = lean_box(0);
lean_ctor_set(x_6, 1, x_143);
lean_ctor_set(x_6, 0, x_195);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_6);
lean_ctor_set(x_196, 1, x_134);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_197 = lean_ctor_get(x_6, 1);
lean_inc(x_197);
lean_dec(x_6);
x_198 = lean_ctor_get(x_5, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_199 = x_5;
} else {
 lean_dec_ref(x_5);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_197, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_197, 4);
lean_inc(x_204);
x_205 = lean_ctor_get(x_197, 5);
lean_inc(x_205);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 lean_ctor_release(x_197, 4);
 lean_ctor_release(x_197, 5);
 x_206 = x_197;
} else {
 lean_dec_ref(x_197);
 x_206 = lean_box(0);
}
x_207 = l_Lake_print_x21___closed__11;
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 6, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_200);
lean_ctor_set(x_208, 1, x_201);
lean_ctor_set(x_208, 2, x_202);
lean_ctor_set(x_208, 3, x_207);
lean_ctor_set(x_208, 4, x_204);
lean_ctor_set(x_208, 5, x_205);
x_209 = lean_string_utf8_byte_size(x_203);
x_210 = lean_unsigned_to_nat(0u);
x_211 = lean_nat_dec_eq(x_209, x_210);
lean_dec(x_209);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_199);
x_212 = lean_ctor_get(x_2, 1);
lean_inc(x_212);
lean_dec(x_2);
x_213 = lean_ctor_get(x_212, 4);
lean_inc(x_213);
lean_inc(x_203);
x_214 = lean_apply_2(x_213, x_203, x_198);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_203);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_apply_1(x_216, x_215);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_208);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_219);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_224 = x_217;
} else {
 lean_dec_ref(x_217);
 x_224 = lean_box(0);
}
x_225 = lean_box(0);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_208);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_224;
 lean_ctor_set_tag(x_227, 0);
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_223);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_228 = lean_ctor_get(x_214, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_214, 1);
lean_inc(x_229);
lean_dec(x_214);
x_230 = lean_io_error_to_string(x_228);
x_231 = l_Lake_print_x21___closed__9;
x_232 = lean_string_append(x_231, x_230);
lean_dec(x_230);
x_233 = l_Lake_print_x21___closed__10;
x_234 = lean_string_append(x_232, x_233);
x_235 = l_String_quote(x_203);
lean_dec(x_203);
x_236 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = l_Std_Format_defWidth;
x_238 = lean_format_pretty(x_236, x_237, x_210, x_210);
x_239 = lean_string_append(x_234, x_238);
lean_dec(x_238);
x_240 = lean_string_append(x_239, x_207);
x_241 = l_Lake_print_x21___closed__12;
x_242 = l_Lake_print_x21___closed__13;
x_243 = lean_unsigned_to_nat(77u);
x_244 = lean_unsigned_to_nat(4u);
x_245 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_241, x_242, x_243, x_244, x_240);
lean_dec(x_240);
x_246 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_245, x_229);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_248 = lean_ctor_get(x_212, 0);
lean_inc(x_248);
lean_dec(x_212);
x_249 = lean_apply_1(x_248, x_247);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_208);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_249, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_256 = x_249;
} else {
 lean_dec_ref(x_249);
 x_256 = lean_box(0);
}
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_208);
if (lean_is_scalar(x_256)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_256;
 lean_ctor_set_tag(x_259, 0);
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_255);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_212);
lean_dec(x_208);
x_260 = lean_ctor_get(x_246, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_246, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_262 = x_246;
} else {
 lean_dec_ref(x_246);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_203);
lean_dec(x_2);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_208);
if (lean_is_scalar(x_199)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_199;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_198);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_2);
x_267 = !lean_is_exclusive(x_5);
if (x_267 == 0)
{
return x_5;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_5, 0);
x_269 = lean_ctor_get(x_5, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_5);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 3, 6);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 4, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 5, x_9);
x_15 = lean_io_mono_ms_now(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_10);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_18);
x_20 = l_Lake_Monitor_main(x_1, x_14, x_19, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
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
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdout(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdout(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdin(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdin(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stderr(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stderr(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stderr(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stderr(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdout(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdout(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdout(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdout(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_9 = x_38;
x_10 = x_48;
goto block_30;
}
else
{
uint8_t x_51; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_38);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_39);
x_58 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_38, 1, x_60);
lean_ctor_set(x_38, 0, x_62);
x_9 = x_38;
x_10 = x_59;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_38);
lean_dec(x_42);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_39, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_71 = x_39;
} else {
 lean_dec_ref(x_39);
 x_71 = lean_box(0);
}
x_72 = lean_get_set_stdin(x_35, x_40);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_9 = x_77;
x_10 = x_73;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_38, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
x_84 = !lean_is_exclusive(x_38);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_38, 0);
x_86 = lean_ctor_get(x_38, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
x_90 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_9 = x_38;
x_10 = x_91;
goto block_30;
}
else
{
uint8_t x_92; 
lean_free_object(x_82);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_38);
lean_dec(x_85);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
lean_inc(x_96);
lean_dec(x_82);
x_99 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_97);
lean_ctor_set(x_38, 1, x_101);
x_9 = x_38;
x_10 = x_100;
goto block_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_38);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_38, 0);
lean_inc(x_106);
lean_dec(x_38);
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_110 = x_82;
} else {
 lean_dec_ref(x_82);
 x_110 = lean_box(0);
}
x_111 = lean_get_set_stdin(x_35, x_83);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 1);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_114;
x_10 = x_112;
goto block_30;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_117 = x_111;
} else {
 lean_dec_ref(x_111);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
x_119 = !lean_is_exclusive(x_37);
if (x_119 == 0)
{
return x_37;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_37, 0);
x_121 = lean_ctor_get(x_37, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_37);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_7);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_34);
if (x_123 == 0)
{
return x_34;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_34, 0);
x_125 = lean_ctor_get(x_34, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_34);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_inc(x_127);
lean_dec(x_7);
x_130 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_128);
x_134 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_133, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_136, sizeof(void*)*2);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_143 = x_136;
} else {
 lean_dec_ref(x_136);
 x_143 = lean_box(0);
}
x_144 = lean_get_set_stdin(x_131, x_137);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 1);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_9 = x_149;
x_10 = x_145;
goto block_30;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_154 = lean_ctor_get(x_135, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_dec(x_134);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_157 = x_135;
} else {
 lean_dec_ref(x_135);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_154, sizeof(void*)*2);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
x_162 = lean_get_set_stdin(x_131, x_155);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_159);
if (lean_is_scalar(x_157)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_157;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
x_9 = x_165;
x_10 = x_163;
goto block_30;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_131);
x_170 = lean_ctor_get(x_134, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_134, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_172 = x_134;
} else {
 lean_dec_ref(x_134);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_130, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_130, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_176 = x_130;
} else {
 lean_dec_ref(x_130);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1;
x_13 = lean_st_mk_ref(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_mk_ref(x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg), 8, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
x_22 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_string_validate_utf8(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
x_37 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_38 = l_panic___at_String_fromUTF8_x21___spec__1(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_23, 0, x_39);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_string_from_utf8_unchecked(x_35);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_23, 0, x_41);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_string_validate_utf8(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
x_46 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_47 = l_panic___at_String_fromUTF8_x21___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
lean_ctor_set(x_23, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_string_from_utf8_unchecked(x_44);
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_27);
lean_ctor_set(x_23, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_24);
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_23);
lean_dec(x_27);
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_24);
x_60 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_58);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_string_validate_utf8(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_67 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_68 = l_panic___at_String_fromUTF8_x21___spec__1(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_69);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_string_from_utf8_unchecked(x_65);
lean_dec(x_65);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_72);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_23);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_23);
lean_dec(x_27);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_23, 0);
lean_inc(x_78);
lean_dec(x_23);
x_79 = lean_ctor_get(x_24, 0);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_82 = x_24;
} else {
 lean_dec_ref(x_24);
 x_82 = lean_box(0);
}
x_83 = lean_st_ref_get(x_17, x_25);
lean_dec(x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 1);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_80);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_string_validate_utf8(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
x_90 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_91 = l_panic___at_String_fromUTF8_x21___spec__1(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_85);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_string_from_utf8_unchecked(x_88);
lean_dec(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_78);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_85);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_101 = x_83;
} else {
 lean_dec_ref(x_83);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_17);
x_103 = !lean_is_exclusive(x_22);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_22, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_23);
if (x_105 == 0)
{
return x_22;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_23, 0);
x_107 = lean_ctor_get(x_23, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_23);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_22, 0, x_108);
return x_22;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_22, 1);
lean_inc(x_109);
lean_dec(x_22);
x_110 = lean_ctor_get(x_23, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_23, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_112 = x_23;
} else {
 lean_dec_ref(x_23);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_17);
x_115 = !lean_is_exclusive(x_22);
if (x_115 == 0)
{
return x_22;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_22, 0);
x_117 = lean_ctor_get(x_22, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_22);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_20);
x_119 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg), 8, 2);
lean_closure_set(x_119, 0, x_20);
lean_closure_set(x_119, 1, x_1);
x_120 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg), 8, 2);
lean_closure_set(x_120, 0, x_20);
lean_closure_set(x_120, 1, x_119);
x_121 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(x_19, x_120, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
x_131 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_string_validate_utf8(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
x_136 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_137 = l_panic___at_String_fromUTF8_x21___spec__1(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_126);
lean_ctor_set(x_122, 0, x_138);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_string_from_utf8_unchecked(x_134);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_122, 0, x_140);
lean_ctor_set(x_131, 0, x_122);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_string_validate_utf8(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_143);
x_145 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_146 = l_panic___at_String_fromUTF8_x21___spec__1(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_126);
lean_ctor_set(x_122, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_122);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_string_from_utf8_unchecked(x_143);
lean_dec(x_143);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_126);
lean_ctor_set(x_122, 0, x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_122);
lean_ctor_set(x_151, 1, x_142);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_123);
lean_dec(x_130);
lean_dec(x_129);
lean_free_object(x_122);
lean_dec(x_126);
x_152 = !lean_is_exclusive(x_131);
if (x_152 == 0)
{
return x_131;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_131, 0);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_131);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_123, 0);
x_157 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
lean_inc(x_156);
lean_dec(x_123);
x_159 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_163 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_158);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_157);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_string_validate_utf8(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_164);
x_166 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_167 = l_panic___at_String_fromUTF8_x21___spec__1(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_168);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_122);
lean_ctor_set(x_169, 1, x_161);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_string_from_utf8_unchecked(x_164);
lean_dec(x_164);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_122, 1, x_163);
lean_ctor_set(x_122, 0, x_171);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_122);
lean_ctor_set(x_172, 1, x_161);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_158);
lean_dec(x_156);
lean_free_object(x_122);
lean_dec(x_126);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_175 = x_159;
} else {
 lean_dec_ref(x_159);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_122, 0);
lean_inc(x_177);
lean_dec(x_122);
x_178 = lean_ctor_get(x_123, 0);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_123, sizeof(void*)*2);
x_180 = lean_ctor_get(x_123, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_181 = x_123;
} else {
 lean_dec_ref(x_123);
 x_181 = lean_box(0);
}
x_182 = lean_st_ref_get(x_17, x_124);
lean_dec(x_17);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 1);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_180);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_179);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_string_validate_utf8(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
x_189 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_190 = l_panic___at_String_fromUTF8_x21___spec__1(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_177);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_185;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_184);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_string_from_utf8_unchecked(x_187);
lean_dec(x_187);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_177);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_186);
if (lean_is_scalar(x_185)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_185;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_184);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
x_198 = lean_ctor_get(x_182, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_182, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_200 = x_182;
} else {
 lean_dec_ref(x_182);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_17);
x_202 = !lean_is_exclusive(x_121);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_121, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_122);
if (x_204 == 0)
{
return x_121;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_122, 0);
x_206 = lean_ctor_get(x_122, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_122);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_121, 0, x_207);
return x_121;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_121, 1);
lean_inc(x_208);
lean_dec(x_121);
x_209 = lean_ctor_get(x_122, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_122, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_211 = x_122;
} else {
 lean_dec_ref(x_122);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_17);
x_214 = !lean_is_exclusive(x_121);
if (x_214 == 0)
{
return x_121;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_121, 0);
x_216 = lean_ctor_get(x_121, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_121);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_14);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_16);
if (x_218 == 0)
{
return x_16;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_16, 0);
x_220 = lean_ctor_get(x_16, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_16);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_13);
if (x_222 == 0)
{
return x_13;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_13, 0);
x_224 = lean_ctor_get(x_13, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_13);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_7, 0);
x_227 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_228 = lean_ctor_get(x_7, 1);
lean_inc(x_228);
lean_inc(x_226);
lean_dec(x_7);
x_229 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1;
x_230 = lean_st_mk_ref(x_229, x_8);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_st_mk_ref(x_229, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_226);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_227);
x_237 = l_IO_FS_Stream_ofBuffer(x_231);
lean_inc(x_234);
x_238 = l_IO_FS_Stream_ofBuffer(x_234);
if (x_2 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__2___rarg), 8, 2);
lean_closure_set(x_239, 0, x_238);
lean_closure_set(x_239, 1, x_1);
x_240 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__3___rarg(x_237, x_239, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_242, sizeof(void*)*2);
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
x_250 = lean_st_ref_get(x_234, x_243);
lean_dec(x_234);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 2, 1);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set_uint8(x_254, sizeof(void*)*2, x_247);
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_string_validate_utf8(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_255);
x_257 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_258 = l_panic___at_String_fromUTF8_x21___spec__1(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_253;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_string_from_utf8_unchecked(x_255);
lean_dec(x_255);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_244);
if (lean_is_scalar(x_245)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_245;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_254);
if (lean_is_scalar(x_253)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_253;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_252);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_266 = lean_ctor_get(x_250, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_250, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_268 = x_250;
} else {
 lean_dec_ref(x_250);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_234);
x_270 = lean_ctor_get(x_240, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_271 = x_240;
} else {
 lean_dec_ref(x_240);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_241, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_241, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_274 = x_241;
} else {
 lean_dec_ref(x_241);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_270);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_234);
x_277 = lean_ctor_get(x_240, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_240, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_279 = x_240;
} else {
 lean_dec_ref(x_240);
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
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_inc(x_238);
x_281 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_Workspace_runFetchM___spec__4___rarg), 8, 2);
lean_closure_set(x_281, 0, x_238);
lean_closure_set(x_281, 1, x_1);
x_282 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_Workspace_runFetchM___spec__5___rarg), 8, 2);
lean_closure_set(x_282, 0, x_238);
lean_closure_set(x_282, 1, x_281);
x_283 = l_IO_withStdin___at_Lake_Workspace_runFetchM___spec__6___rarg(x_237, x_282, x_3, x_4, x_5, x_6, x_236, x_235);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_288 = x_284;
} else {
 lean_dec_ref(x_284);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get_uint8(x_285, sizeof(void*)*2);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
x_293 = lean_st_ref_get(x_234, x_286);
lean_dec(x_234);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_297 = lean_alloc_ctor(0, 2, 1);
} else {
 x_297 = x_292;
}
lean_ctor_set(x_297, 0, x_289);
lean_ctor_set(x_297, 1, x_291);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_290);
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
lean_dec(x_294);
x_299 = lean_string_validate_utf8(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
x_300 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5;
x_301 = l_panic___at_String_fromUTF8_x21___spec__1(x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_288;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_296;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_295);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_string_from_utf8_unchecked(x_298);
lean_dec(x_298);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_287);
if (lean_is_scalar(x_288)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_288;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_297);
if (lean_is_scalar(x_296)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_296;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_295);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_293, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_311 = x_293;
} else {
 lean_dec_ref(x_293);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_234);
x_313 = lean_ctor_get(x_283, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_314 = x_283;
} else {
 lean_dec_ref(x_283);
 x_314 = lean_box(0);
}
x_315 = lean_ctor_get(x_284, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_284, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_317 = x_284;
} else {
 lean_dec_ref(x_284);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_314;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_313);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_234);
x_320 = lean_ctor_get(x_283, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_283, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_322 = x_283;
} else {
 lean_dec_ref(x_283);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = lean_ctor_get(x_233, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_233, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_326 = x_233;
} else {
 lean_dec_ref(x_233);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_328 = lean_ctor_get(x_230, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_230, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_330 = x_230;
} else {
 lean_dec_ref(x_230);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("- ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___closed__1;
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
x_37 = lean_unsigned_to_nat(77u);
x_38 = lean_unsigned_to_nat(4u);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_34);
lean_dec(x_34);
x_40 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_39, x_21);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
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
lean_ctor_set(x_6, 0, x_16);
lean_ctor_set(x_12, 1, x_6);
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
lean_ctor_set(x_6, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_6);
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
lean_ctor_set(x_6, 0, x_22);
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_6);
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
lean_ctor_set(x_6, 0, x_29);
lean_ctor_set(x_12, 1, x_6);
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
lean_ctor_set(x_6, 0, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_6);
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
lean_ctor_set(x_6, 0, x_35);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_10);
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
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_inc(x_43);
lean_dec(x_6);
x_46 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_43, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
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
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_44);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_57 = x_46;
} else {
 lean_dec_ref(x_46);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_60 = x_47;
} else {
 lean_dec_ref(x_47);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_45);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_44);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_45);
x_64 = lean_ctor_get(x_46, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_46, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_66 = x_46;
} else {
 lean_dec_ref(x_46);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_recFetchWithIndex), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_string_utf8_byte_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_19 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_14, x_16, x_17);
x_20 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_14, x_19, x_16);
x_21 = lean_string_utf8_extract(x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
x_22 = l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__2;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_print_x21___closed__11;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_array_push(x_29, x_27);
lean_ctor_set(x_13, 0, x_30);
x_31 = lean_box(0);
x_32 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_15, x_31, x_8, x_2, x_3, x_4, x_13, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_36 = lean_array_push(x_33, x_27);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_34);
x_38 = lean_box(0);
x_39 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_15, x_38, x_8, x_2, x_3, x_4, x_37, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_15, x_40, x_8, x_2, x_3, x_4, x_13, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_9, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
lean_dec(x_9);
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_51 = x_10;
} else {
 lean_dec_ref(x_10);
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
else
{
uint8_t x_54; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
return x_9;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_9, 0);
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_9);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_mkBuildContext___closed__1;
x_2 = 0;
x_3 = l_Lake_BuildTrace_nil;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("job computation", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__3;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Some required builds logged failures:\n", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__5;
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__7;
x_2 = l_Std_Format_defWidth;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("top-level build failed", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_runFetchM___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Workspace_runFetchM___rarg___closed__9;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
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
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg___lambda__1), 7, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_st_mk_ref(x_21, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lake_Workspace_runFetchM___rarg___closed__1;
lean_inc(x_17);
lean_inc(x_23);
x_26 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___rarg___lambda__3), 6, 5);
lean_closure_set(x_26, 0, x_19);
lean_closure_set(x_26, 1, x_20);
lean_closure_set(x_26, 2, x_23);
lean_closure_set(x_26, 3, x_17);
lean_closure_set(x_26, 4, x_25);
x_27 = l_Task_Priority_default;
x_28 = lean_io_as_task(x_26, x_27, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lake_Workspace_runFetchM___rarg___closed__2;
x_32 = 0;
lean_inc(x_29);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
x_34 = lean_st_ref_get(x_23, x_30);
lean_dec(x_23);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_131 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
lean_dec(x_3);
x_132 = 2;
x_133 = l_Lake_instDecidableEqVerbosity(x_131, x_132);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 0, x_33);
x_134 = lean_array_mk(x_34);
if (x_133 == 0)
{
lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_17, 3);
lean_inc(x_135);
lean_dec(x_17);
x_136 = 2;
x_137 = l_Lake_print_x21___closed__11;
x_138 = l_Lake_mkBuildContext___closed__1;
x_139 = lean_unsigned_to_nat(100u);
x_140 = lean_unbox(x_11);
lean_dec(x_11);
lean_inc(x_7);
x_141 = l_Lake_monitorJobs(x_134, x_135, x_7, x_14, x_13, x_136, x_133, x_140, x_15, x_137, x_138, x_139, x_36);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_38 = x_142;
x_39 = x_143;
goto block_130;
}
else
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_144 = lean_ctor_get(x_17, 3);
lean_inc(x_144);
lean_dec(x_17);
x_145 = 0;
x_146 = l_Lake_print_x21___closed__11;
x_147 = l_Lake_mkBuildContext___closed__1;
x_148 = lean_unsigned_to_nat(100u);
x_149 = lean_unbox(x_11);
lean_dec(x_11);
lean_inc(x_7);
x_150 = l_Lake_monitorJobs(x_134, x_144, x_7, x_14, x_13, x_145, x_133, x_149, x_15, x_146, x_147, x_148, x_36);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_38 = x_151;
x_39 = x_152;
goto block_130;
}
block_130:
{
lean_object* x_40; uint8_t x_93; 
x_93 = l_Array_isEmpty___rarg(x_38);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_29);
x_94 = lean_ctor_get(x_7, 4);
lean_inc(x_94);
x_95 = l_Lake_Workspace_runFetchM___rarg___closed__5;
x_96 = lean_apply_2(x_94, x_95, x_39);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_40 = x_97;
goto block_92;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_io_error_to_string(x_98);
x_101 = l_Lake_print_x21___closed__9;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = l_Lake_print_x21___closed__10;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_Lake_Workspace_runFetchM___rarg___closed__8;
x_106 = lean_string_append(x_104, x_105);
x_107 = l_Lake_print_x21___closed__11;
x_108 = lean_string_append(x_106, x_107);
x_109 = l_Lake_print_x21___closed__12;
x_110 = l_Lake_print_x21___closed__13;
x_111 = lean_unsigned_to_nat(77u);
x_112 = lean_unsigned_to_nat(4u);
x_113 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_109, x_110, x_111, x_112, x_108);
lean_dec(x_108);
x_114 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_113, x_99);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_40 = x_115;
goto block_92;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_38);
lean_dec(x_7);
x_116 = lean_io_wait(x_29, x_39);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec(x_117);
lean_ctor_set(x_116, 0, x_120);
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_117);
x_124 = !lean_is_exclusive(x_116);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_116, 0);
lean_dec(x_125);
x_126 = l_Lake_Workspace_runFetchM___rarg___closed__10;
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 0, x_126);
return x_116;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_dec(x_116);
x_128 = l_Lake_Workspace_runFetchM___rarg___closed__10;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
block_92:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_array_get_size(x_38);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_38);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_apply_1(x_44, x_40);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_45, 0);
lean_dec(x_53);
x_54 = l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_ctor_set(x_45, 0, x_54);
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_dec(x_45);
x_56 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_41, x_41);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
lean_dec(x_38);
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_apply_1(x_59, x_40);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_60, 0);
lean_dec(x_68);
x_69 = l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_ctor_set(x_60, 0, x_69);
return x_60;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_dec(x_60);
x_71 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_75 = lean_box(0);
lean_inc(x_7);
x_76 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(x_7, x_38, x_73, x_74, x_75, x_40);
lean_dec(x_38);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_7, 0);
lean_inc(x_78);
lean_dec(x_7);
x_79 = lean_apply_1(x_78, x_77);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_79, 0);
lean_dec(x_87);
x_88 = l_Lake_Workspace_runFetchM___rarg___closed__4;
lean_ctor_set(x_79, 0, x_88);
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_dec(x_79);
x_90 = l_Lake_Workspace_runFetchM___rarg___closed__4;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_231; uint8_t x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; 
x_153 = lean_ctor_get(x_34, 1);
lean_inc(x_153);
lean_dec(x_34);
x_231 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
lean_dec(x_3);
x_232 = 2;
x_233 = l_Lake_instDecidableEqVerbosity(x_231, x_232);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_33);
lean_ctor_set(x_234, 1, x_20);
x_235 = lean_array_mk(x_234);
if (x_233 == 0)
{
lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_236 = lean_ctor_get(x_17, 3);
lean_inc(x_236);
lean_dec(x_17);
x_237 = 2;
x_238 = l_Lake_print_x21___closed__11;
x_239 = l_Lake_mkBuildContext___closed__1;
x_240 = lean_unsigned_to_nat(100u);
x_241 = lean_unbox(x_11);
lean_dec(x_11);
lean_inc(x_7);
x_242 = l_Lake_monitorJobs(x_235, x_236, x_7, x_14, x_13, x_237, x_233, x_241, x_15, x_238, x_239, x_240, x_153);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_154 = x_243;
x_155 = x_244;
goto block_230;
}
else
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_245 = lean_ctor_get(x_17, 3);
lean_inc(x_245);
lean_dec(x_17);
x_246 = 0;
x_247 = l_Lake_print_x21___closed__11;
x_248 = l_Lake_mkBuildContext___closed__1;
x_249 = lean_unsigned_to_nat(100u);
x_250 = lean_unbox(x_11);
lean_dec(x_11);
lean_inc(x_7);
x_251 = l_Lake_monitorJobs(x_235, x_245, x_7, x_14, x_13, x_246, x_233, x_250, x_15, x_247, x_248, x_249, x_153);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_154 = x_252;
x_155 = x_253;
goto block_230;
}
block_230:
{
lean_object* x_156; uint8_t x_197; 
x_197 = l_Array_isEmpty___rarg(x_154);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_29);
x_198 = lean_ctor_get(x_7, 4);
lean_inc(x_198);
x_199 = l_Lake_Workspace_runFetchM___rarg___closed__5;
x_200 = lean_apply_2(x_198, x_199, x_155);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_156 = x_201;
goto block_196;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_io_error_to_string(x_202);
x_205 = l_Lake_print_x21___closed__9;
x_206 = lean_string_append(x_205, x_204);
lean_dec(x_204);
x_207 = l_Lake_print_x21___closed__10;
x_208 = lean_string_append(x_206, x_207);
x_209 = l_Lake_Workspace_runFetchM___rarg___closed__8;
x_210 = lean_string_append(x_208, x_209);
x_211 = l_Lake_print_x21___closed__11;
x_212 = lean_string_append(x_210, x_211);
x_213 = l_Lake_print_x21___closed__12;
x_214 = l_Lake_print_x21___closed__13;
x_215 = lean_unsigned_to_nat(77u);
x_216 = lean_unsigned_to_nat(4u);
x_217 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_213, x_214, x_215, x_216, x_212);
lean_dec(x_212);
x_218 = l_panic___at_Lean_Environment_PromiseCheckedResult_commitChecked___spec__1(x_217, x_203);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_156 = x_219;
goto block_196;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_154);
lean_dec(x_7);
x_220 = lean_io_wait(x_29, x_155);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
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
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
lean_dec(x_221);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_221);
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
x_228 = l_Lake_Workspace_runFetchM___rarg___closed__10;
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_227;
 lean_ctor_set_tag(x_229, 1);
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
return x_229;
}
}
block_196:
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_array_get_size(x_154);
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_nat_dec_lt(x_158, x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_157);
lean_dec(x_154);
x_160 = lean_ctor_get(x_7, 0);
lean_inc(x_160);
lean_dec(x_7);
x_161 = lean_apply_1(x_160, x_156);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = l_Lake_Workspace_runFetchM___rarg___closed__4;
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_163;
 lean_ctor_set_tag(x_165, 1);
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_167 = x_161;
} else {
 lean_dec_ref(x_161);
 x_167 = lean_box(0);
}
x_168 = l_Lake_Workspace_runFetchM___rarg___closed__4;
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = lean_nat_dec_le(x_157, x_157);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_157);
lean_dec(x_154);
x_171 = lean_ctor_get(x_7, 0);
lean_inc(x_171);
lean_dec(x_7);
x_172 = lean_apply_1(x_171, x_156);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = l_Lake_Workspace_runFetchM___rarg___closed__4;
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_174;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
x_179 = l_Lake_Workspace_runFetchM___rarg___closed__4;
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
}
else
{
size_t x_181; size_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = 0;
x_182 = lean_usize_of_nat(x_157);
lean_dec(x_157);
x_183 = lean_box(0);
lean_inc(x_7);
x_184 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(x_7, x_154, x_181, x_182, x_183, x_156);
lean_dec(x_154);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_ctor_get(x_7, 0);
lean_inc(x_186);
lean_dec(x_7);
x_187 = lean_apply_1(x_186, x_185);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = l_Lake_Workspace_runFetchM___rarg___closed__4;
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_189;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_188);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_193 = x_187;
} else {
 lean_dec_ref(x_187);
 x_193 = lean_box(0);
}
x_194 = l_Lake_Workspace_runFetchM___rarg___closed__4;
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
return x_195;
}
}
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Workspace_runFetchM___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
x_19 = l_Lake_Workspace_runFetchM___rarg___closed__4;
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
x_21 = l_Lake_Workspace_runFetchM___rarg___closed__4;
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
x_19 = l_Lake_Workspace_runFetchM___rarg___closed__4;
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
x_21 = l_Lake_Workspace_runFetchM___rarg___closed__4;
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
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_runBuild___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Index(uint8_t builtin, lean_object*);
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
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_Workspace_runFetchM___spec__1___rarg___closed__5);
l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_Workspace_runFetchM___spec__7___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__1 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__1);
l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__2 = _init_l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___lambda__3___closed__2);
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
l_Lake_Workspace_runFetchM___rarg___closed__7 = _init_l_Lake_Workspace_runFetchM___rarg___closed__7();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__7);
l_Lake_Workspace_runFetchM___rarg___closed__8 = _init_l_Lake_Workspace_runFetchM___rarg___closed__8();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__8);
l_Lake_Workspace_runFetchM___rarg___closed__9 = _init_l_Lake_Workspace_runFetchM___rarg___closed__9();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__9);
l_Lake_Workspace_runFetchM___rarg___closed__10 = _init_l_Lake_Workspace_runFetchM___rarg___closed__10();
lean_mark_persistent(l_Lake_Workspace_runFetchM___rarg___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
