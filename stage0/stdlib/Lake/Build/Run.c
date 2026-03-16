// Lean compiler output
// Module: Lake.Build.Run
// Imports: public import Lake.Config.Workspace import Lake.Config.Monad import Lake.Build.Job.Monad import Lake.Build.Index import Init.Omega
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
lean_object* l_Lake_OutStream_get(lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
lean_object* l_instMonadST(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
uint32_t l_Lake_LogLevel_icon(uint8_t);
uint8_t l_Lake_instOrdJobAction_ord(uint8_t, uint8_t);
uint8_t lean_strict_and(uint8_t, uint8_t);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_mono_ms_now();
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static const lean_array_object l_Lake_mkBuildContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_mkBuildContext___closed__0 = (const lean_object*)&l_Lake_mkBuildContext___closed__0_value;
static const lean_string_object l_Lake_mkBuildContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Lean "};
static const lean_object* l_Lake_mkBuildContext___closed__1 = (const lean_object*)&l_Lake_mkBuildContext___closed__1_value;
static lean_once_cell_t l_Lake_mkBuildContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__2;
static const lean_string_object l_Lake_mkBuildContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l_Lake_mkBuildContext___closed__3 = (const lean_object*)&l_Lake_mkBuildContext___closed__3_value;
static lean_once_cell_t l_Lake_mkBuildContext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__4;
static lean_once_cell_t l_Lake_mkBuildContext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__5;
static lean_once_cell_t l_Lake_mkBuildContext___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__6;
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\x1b[2K\r"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Build.Run"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "_private.Lake.Build.Run.0.Lake.print!"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Build"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value),LEAN_SCALAR_PTR_LITERAL(2, 137, 78, 165, 26, 100, 189, 141)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__10 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Run"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__11 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 210, 138, 215, 143, 190, 184, 44)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__12 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(223, 16, 116, 91, 164, 49, 31, 222)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__13 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 129, 2, 182, 107, 115, 87, 113)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__14 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "print!"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__15 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value),LEAN_SCALAR_PTR_LITERAL(171, 56, 2, 158, 131, 186, 32, 163)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__16 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " failed: "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__19 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__21 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Running "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " (+ "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " more)"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ms"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "32"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " (Optional)"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = ": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "- "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Build completed successfully ("};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__0_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ").\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__1_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "All targets up-to-date ("};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " jobs"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "1 job"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Some required targets logged failures:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__6;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__7;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "build failed"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "uncaught top-level build failure (this is likely a bug in Lake)"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "uncaught top-level build failure (this is likely a bug in the build script)"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Workspace_checkNoBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(3, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Workspace_checkNoBuild___redArg___closed__0 = (const lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Workspace_checkNoBuild___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Workspace_checkNoBuild___redArg___closed__1 = (const lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__1_value;
static const lean_string_object l_Lake_Workspace_checkNoBuild___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "job computation"};
static const lean_object* l_Lake_Workspace_checkNoBuild___redArg___closed__2 = (const lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_mkBuildContext___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = l_Lean_versionStringCore;
v___x_5_ = ((lean_object*)(l_Lake_mkBuildContext___closed__1));
v___x_6_ = lean_string_append(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = ((lean_object*)(l_Lake_mkBuildContext___closed__3));
v___x_9_ = lean_obj_once(&l_Lake_mkBuildContext___closed__2, &l_Lake_mkBuildContext___closed__2_once, _init_l_Lake_mkBuildContext___closed__2);
v___x_10_ = lean_string_append(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__5(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_nat_to_int(v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__6(void){
_start:
{
uint32_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = 0;
v___x_14_ = lean_obj_once(&l_Lake_mkBuildContext___closed__5, &l_Lake_mkBuildContext___closed__5_once, _init_l_Lake_mkBuildContext___closed__5);
v___x_15_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set_uint32(v___x_15_, sizeof(void*)*1, v___x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* v_ws_16_, lean_object* v_config_17_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_lakeEnv_21_; lean_object* v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_19_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_20_ = lean_st_mk_ref(v___x_19_);
v_lakeEnv_21_ = lean_ctor_get(v_ws_16_, 1);
v___x_22_ = l_Lake_Env_leanGithash(v_lakeEnv_21_);
v___x_23_ = l_Lake_Hash_nil;
v___x_24_ = lean_string_hash(v___x_22_);
v___x_25_ = lean_uint64_mix_hash(v___x_23_, v___x_24_);
v___x_26_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_27_ = lean_string_append(v___x_26_, v___x_22_);
lean_dec_ref(v___x_22_);
v___x_28_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_29_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_19_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
lean_ctor_set_uint64(v___x_29_, sizeof(void*)*3, v___x_25_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_config_17_);
lean_ctor_set(v___x_30_, 1, v_ws_16_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v___x_20_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object* v_ws_31_, lean_object* v_config_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_mkBuildContext(v_ws_31_, v_config_32_);
return v_res_34_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_35_; lean_object* v___x_36_; 
v___x_35_ = 10493;
v___x_36_ = lean_box_uint32(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_37_; lean_object* v___x_38_; 
v___x_37_ = 10491;
v___x_38_ = lean_box_uint32(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_39_; lean_object* v___x_40_; 
v___x_39_ = 10431;
v___x_40_ = lean_box_uint32(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_41_; lean_object* v___x_42_; 
v___x_41_ = 10367;
v___x_42_ = lean_box_uint32(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_43_; lean_object* v___x_44_; 
v___x_43_ = 10463;
v___x_44_ = lean_box_uint32(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_45_; lean_object* v___x_46_; 
v___x_45_ = 10479;
v___x_46_ = lean_box_uint32(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_47_; lean_object* v___x_48_; 
v___x_47_ = 10487;
v___x_48_ = lean_box_uint32(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8(void){
_start:
{
uint32_t v___x_49_; lean_object* v___x_50_; 
v___x_49_ = 10494;
v___x_50_ = lean_box_uint32(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_51_ = lean_unsigned_to_nat(8u);
v___x_52_ = lean_mk_empty_array_with_capacity(v___x_51_);
v___x_53_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8;
v___x_54_ = lean_array_push(v___x_52_, v___x_53_);
v___x_55_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7;
v___x_56_ = lean_array_push(v___x_54_, v___x_55_);
v___x_57_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6;
v___x_58_ = lean_array_push(v___x_56_, v___x_57_);
v___x_59_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5;
v___x_60_ = lean_array_push(v___x_58_, v___x_59_);
v___x_61_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4;
v___x_62_ = lean_array_push(v___x_60_, v___x_61_);
v___x_63_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3;
v___x_64_ = lean_array_push(v___x_62_, v___x_63_);
v___x_65_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2;
v___x_66_ = lean_array_push(v___x_64_, v___x_65_);
v___x_67_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1;
v___x_68_ = lean_array_push(v___x_66_, v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object* v_out_70_, uint8_t v_outLv_71_, uint8_t v_useAnsi_72_, lean_object* v_e_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lake_logToStream(v_e_73_, v_out_70_, v_outLv_71_, v_useAnsi_72_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object* v_out_76_, lean_object* v_outLv_77_, lean_object* v_useAnsi_78_, lean_object* v_e_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_outLv_boxed_81_; uint8_t v_useAnsi_boxed_82_; lean_object* v_res_83_; 
v_outLv_boxed_81_ = lean_unbox(v_outLv_77_);
v_useAnsi_boxed_82_ = lean_unbox(v_useAnsi_78_);
v_res_83_ = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(v_out_76_, v_outLv_boxed_81_, v_useAnsi_boxed_82_, v_e_79_);
lean_dec_ref(v_e_79_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object* v_ctx_84_){
_start:
{
lean_object* v_out_85_; uint8_t v_outLv_86_; uint8_t v_useAnsi_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___f_90_; 
v_out_85_ = lean_ctor_get(v_ctx_84_, 1);
lean_inc_ref(v_out_85_);
v_outLv_86_ = lean_ctor_get_uint8(v_ctx_84_, sizeof(void*)*3);
v_useAnsi_87_ = lean_ctor_get_uint8(v_ctx_84_, sizeof(void*)*3 + 4);
lean_dec_ref(v_ctx_84_);
v___x_88_ = lean_box(v_outLv_86_);
v___x_89_ = lean_box(v_useAnsi_87_);
v___f_90_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed), 5, 3);
lean_closure_set(v___f_90_, 0, v_out_85_);
lean_closure_set(v___f_90_, 1, v___x_88_);
lean_closure_set(v___f_90_, 2, v___x_89_);
return v___f_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* v_ctx_91_, lean_object* v_s_92_, lean_object* v_self_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_apply_3(v_self_93_, v_ctx_91_, v_s_92_, lean_box(0));
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object* v_ctx_96_, lean_object* v_s_97_, lean_object* v_self_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(v_ctx_96_, v_s_97_, v_self_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* v_00_u03b1_101_, lean_object* v_ctx_102_, lean_object* v_s_103_, lean_object* v_self_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_apply_3(v_self_104_, v_ctx_102_, v_s_103_, lean_box(0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object* v_00_u03b1_107_, lean_object* v_ctx_108_, lean_object* v_s_109_, lean_object* v_self_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run(v_00_u03b1_107_, v_ctx_108_, v_s_109_, v_self_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* v_out_115_){
_start:
{
lean_object* v_flush_117_; lean_object* v___x_118_; 
v_flush_117_ = lean_ctor_get(v_out_115_, 0);
lean_inc_ref(v_flush_117_);
lean_dec_ref(v_out_115_);
v___x_118_ = lean_apply_1(v_flush_117_, lean_box(0));
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v___x_118_);
return v_a_119_;
}
else
{
lean_object* v___x_120_; 
lean_dec_ref(v___x_118_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object* v_out_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lake_Build_Run_0__Lake_flush(v_out_121_);
return v_res_123_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_instMonadST(lean_box(0));
return v___x_124_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_box(0);
v___x_126_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_127_ = l_instInhabitedOfMonad___redArg(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17(void){
_start:
{
uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = 1;
v___x_158_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__17, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
v___x_161_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_162_ = lean_string_append(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_165_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__18, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18);
v___x_166_ = lean_string_append(v___x_165_, v___x_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* v_out_168_, lean_object* v_s_169_){
_start:
{
lean_object* v_putStr_171_; lean_object* v___x_172_; 
v_putStr_171_ = lean_ctor_get(v_out_168_, 4);
lean_inc_ref(v_putStr_171_);
lean_dec_ref(v_out_168_);
lean_inc_ref(v_s_169_);
v___x_172_ = lean_apply_2(v_putStr_171_, v_s_169_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; 
lean_dec_ref(v_s_169_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref(v___x_172_);
return v_a_173_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_199_; 
v_a_174_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_199_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_199_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_199_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_178_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_179_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_180_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_181_ = lean_unsigned_to_nat(89u);
v___x_182_ = lean_unsigned_to_nat(4u);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_185_ = lean_io_error_to_string(v_a_174_);
v___x_186_ = lean_string_append(v___x_184_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
v___x_189_ = l_String_quote(v_s_169_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 3);
lean_ctor_set(v___x_176_, 0, v___x_189_);
v___x_191_ = v___x_176_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_198_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_181__overap_196_; lean_object* v___x_197_; 
v___x_192_ = l_Std_Format_defWidth;
v___x_193_ = l_Std_Format_pretty(v___x_191_, v___x_192_, v___x_183_, v___x_183_);
v___x_194_ = lean_string_append(v___x_188_, v___x_193_);
lean_dec_ref(v___x_193_);
v___x_195_ = l_mkPanicMessageWithDecl(v___x_179_, v___x_180_, v___x_181_, v___x_182_, v___x_194_);
lean_dec_ref(v___x_194_);
v___x_181__overap_196_ = l_panic___redArg(v___x_178_, v___x_195_);
v___x_197_ = lean_apply_1(v___x_181__overap_196_, lean_box(0));
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object* v_out_200_, lean_object* v_s_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lake_Build_Run_0__Lake_print_x21(v_out_200_, v_s_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* v_s_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_val_209_; lean_object* v_out_211_; lean_object* v_putStr_212_; lean_object* v___x_213_; 
v_out_211_ = lean_ctor_get(v_a_205_, 1);
lean_inc_ref(v_out_211_);
lean_dec_ref(v_a_205_);
v_putStr_212_ = lean_ctor_get(v_out_211_, 4);
lean_inc_ref(v_putStr_212_);
lean_dec_ref(v_out_211_);
lean_inc_ref(v_s_204_);
v___x_213_ = lean_apply_2(v_putStr_212_, v_s_204_, lean_box(0));
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; 
lean_dec_ref(v_s_204_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v_val_209_ = v_a_214_;
goto v___jp_208_;
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_240_; 
v_a_215_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_240_ == 0)
{
v___x_217_ = v___x_213_;
v_isShared_218_ = v_isSharedCheck_240_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_240_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_219_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_220_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_221_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_222_ = lean_unsigned_to_nat(89u);
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_226_ = lean_io_error_to_string(v_a_215_);
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
v___x_230_ = l_String_quote(v_s_204_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 3);
lean_ctor_set(v___x_217_, 0, v___x_230_);
v___x_232_ = v___x_217_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_239_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_808__overap_237_; lean_object* v___x_238_; 
v___x_233_ = l_Std_Format_defWidth;
v___x_234_ = l_Std_Format_pretty(v___x_232_, v___x_233_, v___x_224_, v___x_224_);
v___x_235_ = lean_string_append(v___x_229_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = l_mkPanicMessageWithDecl(v___x_220_, v___x_221_, v___x_222_, v___x_223_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_808__overap_237_ = l_panic___redArg(v___x_219_, v___x_236_);
v___x_238_ = lean_apply_1(v___x_808__overap_237_, lean_box(0));
v_val_209_ = v___x_238_;
goto v___jp_208_;
}
}
}
v___jp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_val_209_);
lean_ctor_set(v___x_210_, 1, v_a_206_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object* v_s_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lake_Build_Run_0__Lake_Monitor_print(v_s_241_, v_a_242_, v_a_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_val_250_; lean_object* v_out_252_; lean_object* v_flush_253_; lean_object* v___x_254_; 
v_out_252_ = lean_ctor_get(v_a_246_, 1);
lean_inc_ref(v_out_252_);
lean_dec_ref(v_a_246_);
v_flush_253_ = lean_ctor_get(v_out_252_, 0);
lean_inc_ref(v_flush_253_);
lean_dec_ref(v_out_252_);
v___x_254_ = lean_apply_1(v_flush_253_, lean_box(0));
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v___x_254_);
v_val_250_ = v_a_255_;
goto v___jp_249_;
}
else
{
lean_object* v___x_256_; 
lean_dec_ref(v___x_254_);
v___x_256_ = lean_box(0);
v_val_250_ = v___x_256_;
goto v___jp_249_;
}
v___jp_249_:
{
lean_object* v___x_251_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_val_250_);
lean_ctor_set(v___x_251_, 1, v_a_247_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lake_Build_Run_0__Lake_Monitor_flush(v_a_257_, v_a_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* v_msg_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_9187__overap_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_9187__overap_264_ = lean_panic_fn(v___x_263_, v_msg_261_);
v___x_265_ = lean_apply_1(v___x_9187__overap_264_, lean_box(0));
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object* v_msg_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v_msg_266_);
return v_res_268_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_270_ = lean_array_get_size(v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* v_running_277_, lean_object* v_unfinished_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
uint8_t v_showProgress_285_; 
v_showProgress_285_ = lean_ctor_get_uint8(v_a_279_, sizeof(void*)*3 + 5);
if (v_showProgress_285_ == 0)
{
lean_dec_ref(v_a_279_);
goto v___jp_282_;
}
else
{
uint8_t v_useAnsi_286_; 
v_useAnsi_286_ = lean_ctor_get_uint8(v_a_279_, sizeof(void*)*3 + 4);
if (v_useAnsi_286_ == 0)
{
lean_dec_ref(v_a_279_);
goto v___jp_282_;
}
else
{
lean_object* v_jobNo_287_; lean_object* v_totalJobs_288_; uint8_t v_wantsRebuild_289_; lean_object* v_failures_290_; lean_object* v_resetCtrl_291_; lean_object* v_lastUpdate_292_; lean_object* v_spinnerIdx_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_382_; 
v_jobNo_287_ = lean_ctor_get(v_a_280_, 0);
v_totalJobs_288_ = lean_ctor_get(v_a_280_, 1);
v_wantsRebuild_289_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*6);
v_failures_290_ = lean_ctor_get(v_a_280_, 2);
v_resetCtrl_291_ = lean_ctor_get(v_a_280_, 3);
v_lastUpdate_292_ = lean_ctor_get(v_a_280_, 4);
v_spinnerIdx_293_ = lean_ctor_get(v_a_280_, 5);
v_isSharedCheck_382_ = !lean_is_exclusive(v_a_280_);
if (v_isSharedCheck_382_ == 0)
{
v___x_295_ = v_a_280_;
v_isShared_296_ = v_isSharedCheck_382_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_spinnerIdx_293_);
lean_inc(v_lastUpdate_292_);
lean_inc(v_resetCtrl_291_);
lean_inc(v_failures_290_);
lean_inc(v_totalJobs_288_);
lean_inc(v_jobNo_287_);
lean_dec(v_a_280_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_382_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_out_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v_out_297_ = lean_ctor_get(v_a_279_, 1);
lean_inc_ref(v_out_297_);
lean_dec_ref(v_a_279_);
v___x_298_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_299_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
v___x_300_ = lean_array_fget(v___x_298_, v_spinnerIdx_293_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = l_Fin_add(v___x_299_, v_spinnerIdx_293_, v___x_301_);
lean_dec(v_spinnerIdx_293_);
v___x_303_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(v_totalJobs_288_);
lean_inc(v_jobNo_287_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 5, v___x_302_);
lean_ctor_set(v___x_295_, 3, v___x_303_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_jobNo_287_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_totalJobs_288_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_failures_290_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_lastUpdate_292_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v___x_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*6, v_wantsRebuild_289_);
v___x_305_ = v_reuseFailAlloc_381_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v_val_307_; lean_object* v___y_315_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_array_get_size(v_running_277_);
v___x_363_ = lean_nat_dec_lt(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_caption_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_364_ = lean_array_get_size(v_unfinished_278_);
v___x_365_ = lean_nat_sub(v___x_364_, v___x_301_);
v___x_366_ = lean_array_fget_borrowed(v_unfinished_278_, v___x_365_);
lean_dec(v___x_365_);
v_caption_367_ = lean_ctor_get(v___x_366_, 2);
v___x_368_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_369_ = lean_string_append(v___x_368_, v_caption_367_);
v___y_315_ = v___x_369_;
goto v___jp_314_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_caption_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_370_ = lean_nat_sub(v___x_362_, v___x_301_);
v___x_371_ = lean_array_fget_borrowed(v_running_277_, v___x_370_);
v_caption_372_ = lean_ctor_get(v___x_371_, 2);
v___x_373_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_374_ = lean_string_append(v___x_373_, v_caption_372_);
v___x_375_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
v___x_376_ = lean_string_append(v___x_374_, v___x_375_);
v___x_377_ = l_Nat_reprFast(v___x_370_);
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
v___x_380_ = lean_string_append(v___x_378_, v___x_379_);
v___y_315_ = v___x_380_;
goto v___jp_314_;
}
v___jp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_val_307_);
lean_ctor_set(v___x_308_, 1, v___x_305_);
return v___x_308_;
}
v___jp_309_:
{
lean_object* v_flush_310_; lean_object* v___x_311_; 
v_flush_310_ = lean_ctor_get(v_out_297_, 0);
lean_inc_ref(v_flush_310_);
lean_dec_ref(v_out_297_);
v___x_311_ = lean_apply_1(v_flush_310_, lean_box(0));
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___x_311_);
v_val_307_ = v_a_312_;
goto v___jp_306_;
}
else
{
lean_object* v___x_313_; 
lean_dec_ref(v___x_311_);
v___x_313_ = lean_box(0);
v_val_307_ = v___x_313_;
goto v___jp_306_;
}
}
v___jp_314_:
{
lean_object* v_putStr_316_; lean_object* v___x_317_; uint32_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_putStr_316_ = lean_ctor_get(v_out_297_, 4);
v___x_317_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_318_ = lean_unbox_uint32(v___x_300_);
lean_dec(v___x_300_);
v___x_319_ = lean_string_push(v___x_317_, v___x_318_);
v___x_320_ = lean_string_append(v_resetCtrl_291_, v___x_319_);
lean_dec_ref(v___x_319_);
v___x_321_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
v___x_323_ = l_Nat_reprFast(v_jobNo_287_);
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___x_327_ = l_Nat_reprFast(v_totalJobs_288_);
v___x_328_ = lean_string_append(v___x_326_, v___x_327_);
lean_dec_ref(v___x_327_);
v___x_329_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_330_ = lean_string_append(v___x_328_, v___x_329_);
v___x_331_ = lean_string_append(v___x_330_, v___y_315_);
lean_dec_ref(v___y_315_);
lean_inc_ref(v_putStr_316_);
lean_inc_ref(v___x_331_);
v___x_332_ = lean_apply_2(v_putStr_316_, v___x_331_, lean_box(0));
if (lean_obj_tag(v___x_332_) == 0)
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v___x_331_);
goto v___jp_309_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_360_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_360_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_360_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_360_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_337_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_339_ = lean_unsigned_to_nat(89u);
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_343_, v_useAnsi_286_);
v___x_345_ = lean_string_append(v___x_341_, v___x_344_);
lean_dec_ref(v___x_344_);
v___x_346_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
v___x_348_ = lean_io_error_to_string(v_a_333_);
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
lean_dec_ref(v___x_348_);
v___x_350_ = lean_string_append(v___x_349_, v___x_329_);
v___x_351_ = l_String_quote(v___x_331_);
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 3);
lean_ctor_set(v___x_335_, 0, v___x_351_);
v___x_353_ = v___x_335_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_359_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = l_Std_Format_defWidth;
v___x_355_ = l_Std_Format_pretty(v___x_353_, v___x_354_, v___x_342_, v___x_342_);
v___x_356_ = lean_string_append(v___x_350_, v___x_355_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_mkPanicMessageWithDecl(v___x_337_, v___x_338_, v___x_339_, v___x_340_, v___x_356_);
lean_dec_ref(v___x_356_);
v___x_358_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_357_);
goto v___jp_309_;
}
}
}
}
}
}
}
}
v___jp_282_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_a_280_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* v_running_383_, lean_object* v_unfinished_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_383_, v_unfinished_384_, v_a_385_, v_a_386_);
lean_dec_ref(v_unfinished_384_);
lean_dec_ref(v_running_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* v_running_389_, lean_object* v_unfinished_390_, lean_object* v_h_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_389_, v_unfinished_390_, v_a_392_, v_a_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* v_running_396_, lean_object* v_unfinished_397_, lean_object* v_h_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(v_running_396_, v_unfinished_397_, v_h_398_, v_a_399_, v_a_400_);
lean_dec_ref(v_unfinished_397_);
lean_dec_ref(v_running_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object* v_ms_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(10000u);
v___x_408_ = lean_nat_dec_lt(v___x_407_, v_ms_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(1000u);
v___x_410_ = lean_nat_dec_lt(v___x_409_, v_ms_406_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = l_Nat_reprFast(v_ms_406_);
v___x_412_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_414_ = lean_nat_div(v_ms_406_, v___x_409_);
v___x_415_ = l_Nat_reprFast(v___x_414_);
v___x_416_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(50u);
v___x_419_ = lean_nat_add(v_ms_406_, v___x_418_);
lean_dec(v_ms_406_);
v___x_420_ = lean_unsigned_to_nat(100u);
v___x_421_ = lean_nat_div(v___x_419_, v___x_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_unsigned_to_nat(10u);
v___x_423_ = lean_nat_mod(v___x_421_, v___x_422_);
lean_dec(v___x_421_);
v___x_424_ = l_Nat_reprFast(v___x_423_);
v___x_425_ = lean_string_append(v___x_417_, v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
return v___x_427_;
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_428_ = lean_unsigned_to_nat(1000u);
v___x_429_ = lean_nat_div(v_ms_406_, v___x_428_);
lean_dec(v_ms_406_);
v___x_430_ = l_Nat_reprFast(v___x_429_);
v___x_431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_432_ = lean_string_append(v___x_430_, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* v_out_433_, uint8_t v___y_434_, uint8_t v_useAnsi_435_, lean_object* v_as_436_, size_t v_i_437_, size_t v_stop_438_, lean_object* v_b_439_, lean_object* v___y_440_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_eq(v_i_437_, v_stop_438_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; size_t v___x_445_; size_t v___x_446_; 
v___x_443_ = lean_array_uget_borrowed(v_as_436_, v_i_437_);
lean_inc_ref(v_out_433_);
v___x_444_ = l_Lake_logToStream(v___x_443_, v_out_433_, v___y_434_, v_useAnsi_435_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_437_, v___x_445_);
v_i_437_ = v___x_446_;
v_b_439_ = v___x_444_;
goto _start;
}
else
{
lean_object* v___x_448_; 
lean_dec_ref(v_out_433_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_b_439_);
lean_ctor_set(v___x_448_, 1, v___y_440_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* v_out_449_, lean_object* v___y_450_, lean_object* v_useAnsi_451_, lean_object* v_as_452_, lean_object* v_i_453_, lean_object* v_stop_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v___y_17578__boxed_458_; uint8_t v_useAnsi_17579__boxed_459_; size_t v_i_boxed_460_; size_t v_stop_boxed_461_; lean_object* v_res_462_; 
v___y_17578__boxed_458_ = lean_unbox(v___y_450_);
v_useAnsi_17579__boxed_459_ = lean_unbox(v_useAnsi_451_);
v_i_boxed_460_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_449_, v___y_17578__boxed_458_, v_useAnsi_17579__boxed_459_, v_as_452_, v_i_boxed_460_, v_stop_boxed_461_, v_b_455_, v___y_456_);
lean_dec_ref(v_as_452_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___y_475_; lean_object* v___y_479_; lean_object* v_val_480_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_jobNo_494_; lean_object* v_totalJobs_495_; uint8_t v_wantsRebuild_496_; lean_object* v_failures_497_; lean_object* v_resetCtrl_498_; lean_object* v_lastUpdate_499_; lean_object* v_spinnerIdx_500_; lean_object* v_out_501_; uint8_t v_outLv_502_; uint8_t v_failLv_503_; uint8_t v_minAction_504_; uint8_t v_showOptional_505_; uint8_t v_useAnsi_506_; uint8_t v_showProgress_507_; uint8_t v_showTime_508_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; lean_object* v___y_606_; uint8_t v___y_607_; lean_object* v___y_608_; lean_object* v_task_610_; lean_object* v_caption_611_; uint8_t v_optional_612_; lean_object* v___y_614_; lean_object* v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; uint8_t v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___y_622_; uint32_t v___y_623_; uint8_t v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; uint32_t v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; uint8_t v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; uint32_t v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; uint8_t v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; uint8_t v___y_693_; uint32_t v___y_694_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; uint8_t v___y_702_; uint8_t v___y_703_; uint8_t v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; uint8_t v___y_718_; uint8_t v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; uint8_t v___y_724_; lean_object* v___y_726_; lean_object* v___y_727_; uint8_t v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; lean_object* v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; uint8_t v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; uint8_t v___y_757_; uint8_t v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; uint8_t v___y_763_; uint8_t v___y_764_; lean_object* v___y_779_; lean_object* v___y_780_; uint8_t v___y_781_; uint8_t v___y_782_; uint8_t v___y_783_; uint8_t v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; uint8_t v___y_787_; uint8_t v___y_788_; lean_object* v___y_793_; lean_object* v___y_794_; uint8_t v___y_795_; uint8_t v___y_796_; uint8_t v___y_797_; uint8_t v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; uint8_t v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; uint8_t v___y_814_; lean_object* v___y_819_; lean_object* v___x_830_; lean_object* v_a_831_; 
v_jobNo_494_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_jobNo_494_);
v_totalJobs_495_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_totalJobs_495_);
v_wantsRebuild_496_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*6);
v_failures_497_ = lean_ctor_get(v_a_472_, 2);
v_resetCtrl_498_ = lean_ctor_get(v_a_472_, 3);
v_lastUpdate_499_ = lean_ctor_get(v_a_472_, 4);
v_spinnerIdx_500_ = lean_ctor_get(v_a_472_, 5);
v_out_501_ = lean_ctor_get(v_a_471_, 1);
lean_inc_ref(v_out_501_);
v_outLv_502_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3);
v_failLv_503_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 1);
v_minAction_504_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 2);
v_showOptional_505_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 3);
v_useAnsi_506_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 4);
v_showProgress_507_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 5);
v_showTime_508_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 6);
v_task_610_ = lean_ctor_get(v_job_470_, 0);
lean_inc_ref(v_task_610_);
v_caption_611_ = lean_ctor_get(v_job_470_, 2);
lean_inc_ref(v_caption_611_);
v_optional_612_ = lean_ctor_get_uint8(v_job_470_, sizeof(void*)*3);
lean_dec_ref(v_job_470_);
v___x_830_ = lean_task_get_own(v_task_610_);
v_a_831_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___y_819_ = v_a_831_;
goto v___jp_818_;
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_box(0);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___y_475_);
return v___x_477_;
}
v___jp_478_:
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_val_480_);
lean_ctor_set(v___x_481_, 1, v___y_479_);
return v___x_481_;
}
v___jp_482_:
{
lean_object* v_out_485_; lean_object* v_flush_486_; lean_object* v___x_487_; 
v_out_485_ = lean_ctor_get(v___y_483_, 1);
lean_inc_ref(v_out_485_);
lean_dec_ref(v___y_483_);
v_flush_486_ = lean_ctor_get(v_out_485_, 0);
lean_inc_ref(v_flush_486_);
lean_dec_ref(v_out_485_);
v___x_487_ = lean_apply_1(v_flush_486_, lean_box(0));
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref(v___x_487_);
v___y_479_ = v___y_484_;
v_val_480_ = v_a_488_;
goto v___jp_478_;
}
else
{
lean_object* v___x_489_; 
lean_dec_ref(v___x_487_);
v___x_489_ = lean_box(0);
v___y_479_ = v___y_484_;
v_val_480_ = v___x_489_;
goto v___jp_478_;
}
}
v___jp_490_:
{
lean_object* v_snd_493_; 
v_snd_493_ = lean_ctor_get(v___y_492_, 1);
lean_inc(v_snd_493_);
lean_dec_ref(v___y_492_);
v___y_483_ = v___y_491_;
v___y_484_ = v_snd_493_;
goto v___jp_482_;
}
v___jp_509_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_lt(v___y_514_, v___y_510_);
lean_dec(v___y_514_);
if (v___x_516_ == 0)
{
lean_dec_ref(v___y_513_);
lean_dec(v___y_510_);
lean_dec_ref(v_out_501_);
v___y_483_ = v___y_511_;
v___y_484_ = v___y_512_;
goto v___jp_482_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_nat_dec_le(v___y_510_, v___y_510_);
if (v___x_518_ == 0)
{
if (v___x_516_ == 0)
{
lean_dec_ref(v___y_513_);
lean_dec(v___y_510_);
lean_dec_ref(v_out_501_);
v___y_483_ = v___y_511_;
v___y_484_ = v___y_512_;
goto v___jp_482_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___y_510_);
lean_dec(v___y_510_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_501_, v___y_515_, v_useAnsi_506_, v___y_513_, v___x_519_, v___x_520_, v___x_517_, v___y_512_);
lean_dec_ref(v___y_513_);
v___y_491_ = v___y_511_;
v___y_492_ = v___x_521_;
goto v___jp_490_;
}
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___y_510_);
lean_dec(v___y_510_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_501_, v___y_515_, v_useAnsi_506_, v___y_513_, v___x_522_, v___x_523_, v___x_517_, v___y_512_);
lean_dec_ref(v___y_513_);
v___y_491_ = v___y_511_;
v___y_492_ = v___x_524_;
goto v___jp_490_;
}
}
}
v___jp_525_:
{
if (v___y_529_ == 0)
{
lean_dec(v___y_532_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_526_);
lean_dec_ref(v_out_501_);
v___y_483_ = v___y_527_;
v___y_484_ = v___y_528_;
goto v___jp_482_;
}
else
{
if (v___y_531_ == 0)
{
v___y_510_ = v___y_526_;
v___y_511_ = v___y_527_;
v___y_512_ = v___y_528_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_532_;
v___y_515_ = v_outLv_502_;
goto v___jp_509_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = 0;
v___y_510_ = v___y_526_;
v___y_511_ = v___y_527_;
v___y_512_ = v___y_528_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_532_;
v___y_515_ = v___x_533_;
goto v___jp_509_;
}
}
}
v___jp_534_:
{
lean_object* v_out_544_; lean_object* v_jobNo_545_; lean_object* v_totalJobs_546_; uint8_t v_wantsRebuild_547_; lean_object* v_failures_548_; lean_object* v_resetCtrl_549_; lean_object* v_lastUpdate_550_; lean_object* v_spinnerIdx_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_597_; 
v_out_544_ = lean_ctor_get(v___y_536_, 1);
v_jobNo_545_ = lean_ctor_get(v___y_537_, 0);
v_totalJobs_546_ = lean_ctor_get(v___y_537_, 1);
v_wantsRebuild_547_ = lean_ctor_get_uint8(v___y_537_, sizeof(void*)*6);
v_failures_548_ = lean_ctor_get(v___y_537_, 2);
v_resetCtrl_549_ = lean_ctor_get(v___y_537_, 3);
v_lastUpdate_550_ = lean_ctor_get(v___y_537_, 4);
v_spinnerIdx_551_ = lean_ctor_get(v___y_537_, 5);
v_isSharedCheck_597_ = !lean_is_exclusive(v___y_537_);
if (v_isSharedCheck_597_ == 0)
{
v___x_553_ = v___y_537_;
v_isShared_554_ = v_isSharedCheck_597_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_spinnerIdx_551_);
lean_inc(v_lastUpdate_550_);
lean_inc(v_resetCtrl_549_);
lean_inc(v_failures_548_);
lean_inc(v_totalJobs_546_);
lean_inc(v_jobNo_545_);
lean_dec(v___y_537_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_597_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_putStr_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v_putStr_555_ = lean_ctor_get(v_out_544_, 4);
v___x_556_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 3, v___x_556_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_jobNo_545_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_totalJobs_546_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_failures_548_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_lastUpdate_550_);
lean_ctor_set(v_reuseFailAlloc_596_, 5, v_spinnerIdx_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*6, v_wantsRebuild_547_);
v___x_558_ = v_reuseFailAlloc_596_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_string_append(v_resetCtrl_549_, v___y_543_);
lean_dec_ref(v___y_543_);
v___x_560_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_561_ = lean_string_append(v___x_559_, v___x_560_);
lean_inc_ref(v_putStr_555_);
lean_inc_ref(v___x_561_);
v___x_562_ = lean_apply_2(v_putStr_555_, v___x_561_, lean_box(0));
if (lean_obj_tag(v___x_562_) == 0)
{
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_561_);
v___y_526_ = v___y_535_;
v___y_527_ = v___y_536_;
v___y_528_ = v___x_558_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_539_;
v___y_531_ = v___y_541_;
v___y_532_ = v___y_540_;
goto v___jp_525_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_595_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_595_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_595_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_595_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_567_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_568_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_569_ = lean_unsigned_to_nat(89u);
v___x_570_ = lean_unsigned_to_nat(4u);
v___x_571_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_572_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7));
v___x_573_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12));
lean_inc(v___y_540_);
v___x_574_ = l_Lean_Name_num___override(v___x_573_, v___y_540_);
v___x_575_ = l_Lean_Name_str___override(v___x_574_, v___x_572_);
v___x_576_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_577_ = l_Lean_Name_str___override(v___x_575_, v___x_576_);
v___x_578_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_577_, v___y_542_);
v___x_579_ = lean_string_append(v___x_571_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = lean_io_error_to_string(v_a_563_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_585_ = lean_string_append(v___x_583_, v___x_584_);
v___x_586_ = l_String_quote(v___x_561_);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 3);
lean_ctor_set(v___x_565_, 0, v___x_586_);
v___x_588_ = v___x_565_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_594_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = l_Std_Format_defWidth;
lean_inc_n(v___y_540_, 2);
v___x_590_ = l_Std_Format_pretty(v___x_588_, v___x_589_, v___y_540_, v___y_540_);
v___x_591_ = lean_string_append(v___x_585_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = l_mkPanicMessageWithDecl(v___x_567_, v___x_568_, v___x_569_, v___x_570_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_592_);
v___y_526_ = v___y_535_;
v___y_527_ = v___y_536_;
v___y_528_ = v___x_558_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_539_;
v___y_531_ = v___y_541_;
v___y_532_ = v___y_540_;
goto v___jp_525_;
}
}
}
}
}
}
v___jp_598_:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lake_Ansi_chalk(v___y_608_, v___y_601_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_608_);
v___y_535_ = v___y_599_;
v___y_536_ = v___y_600_;
v___y_537_ = v___y_602_;
v___y_538_ = v___y_603_;
v___y_539_ = v___y_604_;
v___y_540_ = v___y_606_;
v___y_541_ = v___y_605_;
v___y_542_ = v___y_607_;
v___y_543_ = v___x_609_;
goto v___jp_534_;
}
v___jp_613_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_627_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_628_ = lean_string_push(v___x_627_, v___y_623_);
v___x_629_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
v___x_631_ = l_Nat_reprFast(v_jobNo_494_);
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = l_Nat_reprFast(v_totalJobs_495_);
v___x_636_ = lean_string_append(v___x_634_, v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
v___x_638_ = lean_string_append(v___x_636_, v___x_637_);
v___x_639_ = lean_string_append(v___x_638_, v___y_618_);
lean_dec_ref(v___y_618_);
v___x_640_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
v___x_642_ = lean_string_append(v___x_641_, v___y_614_);
lean_dec_ref(v___y_614_);
v___x_643_ = lean_string_append(v___x_642_, v___x_640_);
v___x_644_ = lean_string_append(v___x_643_, v_caption_611_);
lean_dec_ref(v_caption_611_);
v___x_645_ = lean_string_append(v___x_644_, v___y_626_);
lean_dec_ref(v___y_626_);
if (v_useAnsi_506_ == 0)
{
v___y_535_ = v___y_620_;
v___y_536_ = v___y_621_;
v___y_537_ = v___y_615_;
v___y_538_ = v___y_616_;
v___y_539_ = v___y_617_;
v___y_540_ = v___y_625_;
v___y_541_ = v___y_624_;
v___y_542_ = v___y_619_;
v___y_543_ = v___x_645_;
goto v___jp_534_;
}
else
{
if (v___y_616_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_599_ = v___y_620_;
v___y_600_ = v___y_621_;
v___y_601_ = v___x_645_;
v___y_602_ = v___y_615_;
v___y_603_ = v___y_616_;
v___y_604_ = v___y_617_;
v___y_605_ = v___y_624_;
v___y_606_ = v___y_625_;
v___y_607_ = v___y_619_;
v___y_608_ = v___x_646_;
goto v___jp_598_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_Lake_LogLevel_ansiColor(v___y_622_);
v___y_599_ = v___y_620_;
v___y_600_ = v___y_621_;
v___y_601_ = v___x_645_;
v___y_602_ = v___y_615_;
v___y_603_ = v___y_616_;
v___y_604_ = v___y_617_;
v___y_605_ = v___y_624_;
v___y_606_ = v___y_625_;
v___y_607_ = v___y_619_;
v___y_608_ = v___x_647_;
goto v___jp_598_;
}
}
}
v___jp_648_:
{
lean_object* v___x_661_; 
v___x_661_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_614_ = v___y_649_;
v___y_615_ = v___y_650_;
v___y_616_ = v___y_651_;
v___y_617_ = v___y_652_;
v___y_618_ = v___y_653_;
v___y_619_ = v___y_654_;
v___y_620_ = v___y_655_;
v___y_621_ = v___y_656_;
v___y_622_ = v___y_657_;
v___y_623_ = v___y_658_;
v___y_624_ = v___y_659_;
v___y_625_ = v___y_660_;
v___y_626_ = v___x_661_;
goto v___jp_613_;
}
v___jp_662_:
{
if (v_showTime_508_ == 0)
{
lean_dec(v___y_663_);
v___y_649_ = v___y_664_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_666_;
v___y_652_ = v___y_667_;
v___y_653_ = v___y_675_;
v___y_654_ = v___y_668_;
v___y_655_ = v___y_669_;
v___y_656_ = v___y_670_;
v___y_657_ = v___y_671_;
v___y_658_ = v___y_672_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
goto v___jp_648_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_lt(v___y_674_, v___y_663_);
if (v___x_676_ == 0)
{
lean_dec(v___y_663_);
v___y_649_ = v___y_664_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_666_;
v___y_652_ = v___y_667_;
v___y_653_ = v___y_675_;
v___y_654_ = v___y_668_;
v___y_655_ = v___y_669_;
v___y_656_ = v___y_670_;
v___y_657_ = v___y_671_;
v___y_658_ = v___y_672_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
goto v___jp_648_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_678_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_663_);
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___y_614_ = v___y_664_;
v___y_615_ = v___y_665_;
v___y_616_ = v___y_666_;
v___y_617_ = v___y_667_;
v___y_618_ = v___y_675_;
v___y_619_ = v___y_668_;
v___y_620_ = v___y_669_;
v___y_621_ = v___y_670_;
v___y_622_ = v___y_671_;
v___y_623_ = v___y_672_;
v___y_624_ = v___y_673_;
v___y_625_ = v___y_674_;
v___y_626_ = v___x_681_;
goto v___jp_613_;
}
}
}
v___jp_682_:
{
if (v_optional_612_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_663_ = v___y_685_;
v___y_664_ = v___y_686_;
v___y_665_ = v___y_687_;
v___y_666_ = v___y_689_;
v___y_667_ = v___y_690_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_683_;
v___y_670_ = v___y_684_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_694_;
v___y_673_ = v___y_692_;
v___y_674_ = v___y_691_;
v___y_675_ = v___x_695_;
goto v___jp_662_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_663_ = v___y_685_;
v___y_664_ = v___y_686_;
v___y_665_ = v___y_687_;
v___y_666_ = v___y_689_;
v___y_667_ = v___y_690_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_683_;
v___y_670_ = v___y_684_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_694_;
v___y_673_ = v___y_692_;
v___y_674_ = v___y_691_;
v___y_675_ = v___x_696_;
goto v___jp_662_;
}
}
v___jp_697_:
{
if (v___y_703_ == 0)
{
if (v_showProgress_507_ == 0)
{
lean_dec(v___y_707_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v_caption_611_);
lean_dec_ref(v_out_501_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_701_;
goto v___jp_474_;
}
else
{
if (v_useAnsi_506_ == 0)
{
if (v___y_708_ == 0)
{
lean_dec(v___y_707_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v_caption_611_);
lean_dec_ref(v_out_501_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_701_;
goto v___jp_474_;
}
else
{
lean_object* v___x_709_; uint32_t v___x_710_; 
v___x_709_ = l_Lake_JobAction_verb(v___y_706_, v___y_704_);
v___x_710_ = 10004;
v___y_683_ = v___y_698_;
v___y_684_ = v___y_699_;
v___y_685_ = v___y_700_;
v___y_686_ = v___x_709_;
v___y_687_ = v___y_701_;
v___y_688_ = v___y_702_;
v___y_689_ = v___y_703_;
v___y_690_ = v___y_705_;
v___y_691_ = v___y_707_;
v___y_692_ = v___y_706_;
v___y_693_ = v___y_708_;
v___y_694_ = v___x_710_;
goto v___jp_682_;
}
}
else
{
lean_dec(v___y_707_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v_caption_611_);
lean_dec_ref(v_out_501_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_701_;
goto v___jp_474_;
}
}
}
else
{
lean_object* v___x_711_; uint32_t v___x_712_; 
v___x_711_ = l_Lake_JobAction_verb(v___y_706_, v___y_704_);
v___x_712_ = l_Lake_LogLevel_icon(v___y_702_);
v___y_683_ = v___y_698_;
v___y_684_ = v___y_699_;
v___y_685_ = v___y_700_;
v___y_686_ = v___x_711_;
v___y_687_ = v___y_701_;
v___y_688_ = v___y_702_;
v___y_689_ = v___y_703_;
v___y_690_ = v___y_705_;
v___y_691_ = v___y_707_;
v___y_692_ = v___y_706_;
v___y_693_ = v___y_703_;
v___y_694_ = v___x_712_;
goto v___jp_682_;
}
}
v___jp_713_:
{
if (v_optional_612_ == 0)
{
v___y_698_ = v___y_714_;
v___y_699_ = v___y_715_;
v___y_700_ = v___y_716_;
v___y_701_ = v___y_717_;
v___y_702_ = v___y_718_;
v___y_703_ = v___y_724_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_721_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_723_;
goto v___jp_697_;
}
else
{
if (v_showOptional_505_ == 0)
{
lean_dec(v___y_722_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_caption_611_);
lean_dec_ref(v_out_501_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_717_;
goto v___jp_474_;
}
else
{
v___y_698_ = v___y_714_;
v___y_699_ = v___y_715_;
v___y_700_ = v___y_716_;
v___y_701_ = v___y_717_;
v___y_702_ = v___y_718_;
v___y_703_ = v___y_724_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_721_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_723_;
goto v___jp_697_;
}
}
}
v___jp_725_:
{
if (v___y_732_ == 0)
{
if (v___y_728_ == 0)
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_736_;
v___y_716_ = v___y_727_;
v___y_717_ = v___y_737_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_730_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_728_;
goto v___jp_713_;
}
else
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_736_;
v___y_716_ = v___y_727_;
v___y_717_ = v___y_737_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_730_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_735_;
goto v___jp_713_;
}
}
else
{
if (v_optional_612_ == 0)
{
lean_object* v_jobNo_738_; lean_object* v_totalJobs_739_; uint8_t v_wantsRebuild_740_; lean_object* v_failures_741_; lean_object* v_resetCtrl_742_; lean_object* v_lastUpdate_743_; lean_object* v_spinnerIdx_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_jobNo_738_ = lean_ctor_get(v___y_737_, 0);
v_totalJobs_739_ = lean_ctor_get(v___y_737_, 1);
v_wantsRebuild_740_ = lean_ctor_get_uint8(v___y_737_, sizeof(void*)*6);
v_failures_741_ = lean_ctor_get(v___y_737_, 2);
v_resetCtrl_742_ = lean_ctor_get(v___y_737_, 3);
v_lastUpdate_743_ = lean_ctor_get(v___y_737_, 4);
v_spinnerIdx_744_ = lean_ctor_get(v___y_737_, 5);
v_isSharedCheck_752_ = !lean_is_exclusive(v___y_737_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v___y_737_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_spinnerIdx_744_);
lean_inc(v_lastUpdate_743_);
lean_inc(v_resetCtrl_742_);
lean_inc(v_failures_741_);
lean_inc(v_totalJobs_739_);
lean_inc(v_jobNo_738_);
lean_dec(v___y_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_inc_ref(v_caption_611_);
v___x_748_ = lean_array_push(v_failures_741_, v_caption_611_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 2, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_jobNo_738_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_totalJobs_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_resetCtrl_742_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_lastUpdate_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v_spinnerIdx_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_751_, sizeof(void*)*6, v_wantsRebuild_740_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_736_;
v___y_716_ = v___y_727_;
v___y_717_ = v___x_750_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_730_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_732_;
goto v___jp_713_;
}
}
}
else
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_736_;
v___y_716_ = v___y_727_;
v___y_717_ = v___y_737_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_730_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_732_;
goto v___jp_713_;
}
}
}
v___jp_753_:
{
if (v___y_756_ == 0)
{
v___y_726_ = v___y_754_;
v___y_727_ = v___y_755_;
v___y_728_ = v___y_757_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_759_;
v___y_731_ = v___y_760_;
v___y_732_ = v___y_761_;
v___y_733_ = v___y_762_;
v___y_734_ = v___y_764_;
v___y_735_ = v___y_763_;
v___y_736_ = v_a_471_;
v___y_737_ = v_a_472_;
goto v___jp_725_;
}
else
{
if (v_wantsRebuild_496_ == 0)
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_inc(v_spinnerIdx_500_);
lean_inc(v_lastUpdate_499_);
lean_inc_ref(v_resetCtrl_498_);
lean_inc_ref(v_failures_497_);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_772_ = lean_ctor_get(v_a_472_, 5);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_a_472_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_a_472_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_a_472_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_a_472_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_a_472_, 0);
lean_dec(v_unused_777_);
v___x_766_ = v_a_472_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_dec(v_a_472_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
lean_inc(v_totalJobs_495_);
lean_inc(v_jobNo_494_);
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_jobNo_494_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_totalJobs_495_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_failures_497_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_resetCtrl_498_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_lastUpdate_499_);
lean_ctor_set(v_reuseFailAlloc_770_, 5, v_spinnerIdx_500_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*6, v___y_756_);
v___y_726_ = v___y_754_;
v___y_727_ = v___y_755_;
v___y_728_ = v___y_757_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_759_;
v___y_731_ = v___y_760_;
v___y_732_ = v___y_761_;
v___y_733_ = v___y_762_;
v___y_734_ = v___y_764_;
v___y_735_ = v___y_763_;
v___y_736_ = v_a_471_;
v___y_737_ = v___x_769_;
goto v___jp_725_;
}
}
}
else
{
v___y_726_ = v___y_754_;
v___y_727_ = v___y_755_;
v___y_728_ = v___y_757_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_759_;
v___y_731_ = v___y_760_;
v___y_732_ = v___y_761_;
v___y_733_ = v___y_762_;
v___y_734_ = v___y_764_;
v___y_735_ = v___y_763_;
v___y_736_ = v_a_471_;
v___y_737_ = v_a_472_;
goto v___jp_725_;
}
}
}
v___jp_778_:
{
uint8_t v___x_789_; 
v___x_789_ = l_Lake_instOrdJobAction_ord(v_minAction_504_, v___y_784_);
if (v___x_789_ == 2)
{
uint8_t v___x_790_; 
v___x_790_ = 0;
v___y_754_ = v___y_779_;
v___y_755_ = v___y_780_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_783_;
v___y_759_ = v___y_784_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_787_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_788_;
v___y_764_ = v___x_790_;
goto v___jp_753_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = 1;
v___y_754_ = v___y_779_;
v___y_755_ = v___y_780_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_783_;
v___y_759_ = v___y_784_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_787_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_788_;
v___y_764_ = v___x_791_;
goto v___jp_753_;
}
}
v___jp_792_:
{
uint8_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_strict_and(v___y_796_, v___y_801_);
v___x_803_ = l_Lake_instOrdLogLevel_ord(v_outLv_502_, v___y_797_);
if (v___x_803_ == 2)
{
uint8_t v___x_804_; 
v___x_804_ = 0;
v___y_779_ = v___y_793_;
v___y_780_ = v___y_794_;
v___y_781_ = v___y_796_;
v___y_782_ = v___y_795_;
v___y_783_ = v___y_797_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_799_;
v___y_786_ = v___y_800_;
v___y_787_ = v___x_802_;
v___y_788_ = v___x_804_;
goto v___jp_778_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 1;
v___y_779_ = v___y_793_;
v___y_780_ = v___y_794_;
v___y_781_ = v___y_796_;
v___y_782_ = v___y_795_;
v___y_783_ = v___y_797_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_799_;
v___y_786_ = v___y_800_;
v___y_787_ = v___x_802_;
v___y_788_ = v___x_805_;
goto v___jp_778_;
}
}
v___jp_806_:
{
uint8_t v___x_815_; 
v___x_815_ = l_Lake_instOrdLogLevel_ord(v_failLv_503_, v___y_810_);
if (v___x_815_ == 2)
{
uint8_t v___x_816_; 
v___x_816_ = 0;
v___y_793_ = v___y_807_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_814_;
v___y_797_ = v___y_810_;
v___y_798_ = v___y_811_;
v___y_799_ = v___y_812_;
v___y_800_ = v___y_813_;
v___y_801_ = v___x_816_;
goto v___jp_792_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 1;
v___y_793_ = v___y_807_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_814_;
v___y_797_ = v___y_810_;
v___y_798_ = v___y_811_;
v___y_799_ = v___y_812_;
v___y_800_ = v___y_813_;
v___y_801_ = v___x_817_;
goto v___jp_792_;
}
}
v___jp_818_:
{
lean_object* v_log_820_; uint8_t v_action_821_; uint8_t v_wantsRebuild_822_; lean_object* v_buildTime_823_; uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_log_820_ = lean_ctor_get(v___y_819_, 0);
lean_inc_ref(v_log_820_);
v_action_821_ = lean_ctor_get_uint8(v___y_819_, sizeof(void*)*3);
v_wantsRebuild_822_ = lean_ctor_get_uint8(v___y_819_, sizeof(void*)*3 + 1);
v_buildTime_823_ = lean_ctor_get(v___y_819_, 2);
lean_inc(v_buildTime_823_);
lean_dec_ref(v___y_819_);
v___x_824_ = l_Lake_Log_maxLv(v_log_820_);
v___x_825_ = lean_array_get_size(v_log_820_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
uint8_t v___x_828_; 
v___x_828_ = 1;
v___y_807_ = v___x_825_;
v___y_808_ = v_buildTime_823_;
v___y_809_ = v_wantsRebuild_822_;
v___y_810_ = v___x_824_;
v___y_811_ = v_action_821_;
v___y_812_ = v_log_820_;
v___y_813_ = v___x_826_;
v___y_814_ = v___x_828_;
goto v___jp_806_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = 0;
v___y_807_ = v___x_825_;
v___y_808_ = v_buildTime_823_;
v___y_809_ = v_wantsRebuild_822_;
v___y_810_ = v___x_824_;
v___y_811_ = v_action_821_;
v___y_812_ = v_log_820_;
v___y_813_ = v___x_826_;
v___y_814_ = v___x_829_;
goto v___jp_806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_832_, v_a_833_, v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_837_, uint8_t v___y_838_, uint8_t v_useAnsi_839_, lean_object* v_as_840_, size_t v_i_841_, size_t v_stop_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_837_, v___y_838_, v_useAnsi_839_, v_as_840_, v_i_841_, v_stop_842_, v_b_843_, v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_848_, lean_object* v___y_849_, lean_object* v_useAnsi_850_, lean_object* v_as_851_, lean_object* v_i_852_, lean_object* v_stop_853_, lean_object* v_b_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___y_18355__boxed_858_; uint8_t v_useAnsi_18356__boxed_859_; size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v___y_18355__boxed_858_ = lean_unbox(v___y_849_);
v_useAnsi_18356__boxed_859_ = lean_unbox(v_useAnsi_850_);
v_i_boxed_860_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_848_, v___y_18355__boxed_858_, v_useAnsi_18356__boxed_859_, v_as_851_, v_i_boxed_860_, v_stop_boxed_861_, v_b_854_, v___y_855_, v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v_as_851_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object* v_as_863_, size_t v_i_864_, size_t v_stop_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_fst_871_; lean_object* v_snd_872_; uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_eq(v_i_864_, v_stop_865_);
if (v___x_876_ == 0)
{
lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v___x_879_; lean_object* v_task_880_; uint8_t v___x_881_; 
v_fst_877_ = lean_ctor_get(v_b_866_, 0);
v_snd_878_ = lean_ctor_get(v_b_866_, 1);
v___x_879_ = lean_array_uget_borrowed(v_as_863_, v_i_864_);
v_task_880_ = lean_ctor_get(v___x_879_, 0);
v___x_881_ = lean_io_get_task_state(v_task_880_);
switch(v___x_881_)
{
case 0:
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
lean_inc(v_snd_878_);
lean_inc(v_fst_877_);
v_isSharedCheck_889_ = !lean_is_exclusive(v_b_866_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_890_ = lean_ctor_get(v_b_866_, 1);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_b_866_, 0);
lean_dec(v_unused_891_);
v___x_883_ = v_b_866_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_b_866_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
lean_inc(v___x_879_);
v___x_885_ = lean_array_push(v_snd_878_, v___x_879_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
v_fst_871_ = v___x_887_;
v_snd_872_ = v___y_868_;
goto v___jp_870_;
}
}
}
case 1:
{
lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_900_; 
lean_inc(v_snd_878_);
lean_inc(v_fst_877_);
v_isSharedCheck_900_ = !lean_is_exclusive(v_b_866_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; lean_object* v_unused_902_; 
v_unused_901_ = lean_ctor_get(v_b_866_, 1);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_b_866_, 0);
lean_dec(v_unused_902_);
v___x_893_ = v_b_866_;
v_isShared_894_ = v_isSharedCheck_900_;
goto v_resetjp_892_;
}
else
{
lean_dec(v_b_866_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_900_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
lean_inc(v___x_879_);
v___x_895_ = lean_array_push(v_fst_877_, v___x_879_);
lean_inc(v___x_879_);
v___x_896_ = lean_array_push(v_snd_878_, v___x_879_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v___x_896_);
lean_ctor_set(v___x_893_, 0, v___x_895_);
v___x_898_ = v___x_893_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
v_fst_871_ = v___x_898_;
v_snd_872_ = v___y_868_;
goto v___jp_870_;
}
}
}
default: 
{
lean_object* v___x_903_; lean_object* v_snd_904_; lean_object* v_jobNo_905_; lean_object* v_totalJobs_906_; uint8_t v_wantsRebuild_907_; lean_object* v_failures_908_; lean_object* v_resetCtrl_909_; lean_object* v_lastUpdate_910_; lean_object* v_spinnerIdx_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_920_; 
lean_inc_ref(v___y_867_);
lean_inc(v___x_879_);
v___x_903_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_879_, v___y_867_, v___y_868_);
v_snd_904_ = lean_ctor_get(v___x_903_, 1);
lean_inc(v_snd_904_);
lean_dec_ref(v___x_903_);
v_jobNo_905_ = lean_ctor_get(v_snd_904_, 0);
v_totalJobs_906_ = lean_ctor_get(v_snd_904_, 1);
v_wantsRebuild_907_ = lean_ctor_get_uint8(v_snd_904_, sizeof(void*)*6);
v_failures_908_ = lean_ctor_get(v_snd_904_, 2);
v_resetCtrl_909_ = lean_ctor_get(v_snd_904_, 3);
v_lastUpdate_910_ = lean_ctor_get(v_snd_904_, 4);
v_spinnerIdx_911_ = lean_ctor_get(v_snd_904_, 5);
v_isSharedCheck_920_ = !lean_is_exclusive(v_snd_904_);
if (v_isSharedCheck_920_ == 0)
{
v___x_913_ = v_snd_904_;
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_spinnerIdx_911_);
lean_inc(v_lastUpdate_910_);
lean_inc(v_resetCtrl_909_);
lean_inc(v_failures_908_);
lean_inc(v_totalJobs_906_);
lean_inc(v_jobNo_905_);
lean_dec(v_snd_904_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_jobNo_905_, v___x_915_);
lean_dec(v_jobNo_905_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_totalJobs_906_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_failures_908_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_resetCtrl_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_lastUpdate_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_spinnerIdx_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6, v_wantsRebuild_907_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
v_fst_871_ = v_b_866_;
v_snd_872_ = v___x_918_;
goto v___jp_870_;
}
}
}
}
}
else
{
lean_object* v___x_921_; 
lean_dec_ref(v___y_867_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_b_866_);
lean_ctor_set(v___x_921_, 1, v___y_868_);
return v___x_921_;
}
v___jp_870_:
{
size_t v___x_873_; size_t v___x_874_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_864_, v___x_873_);
v_i_864_ = v___x_874_;
v_b_866_ = v_fst_871_;
v___y_868_ = v_snd_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object* v_as_922_, lean_object* v_i_923_, lean_object* v_stop_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
size_t v_i_boxed_929_; size_t v_stop_boxed_930_; lean_object* v_res_931_; 
v_i_boxed_929_ = lean_unbox_usize(v_i_923_);
lean_dec(v_i_923_);
v_stop_boxed_930_ = lean_unbox_usize(v_stop_924_);
lean_dec(v_stop_924_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v_as_922_, v_i_boxed_929_, v_stop_boxed_930_, v_b_925_, v___y_926_, v___y_927_);
lean_dec_ref(v_as_922_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object* v_unfinished_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_jobs_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v_jobNo_943_; lean_object* v_totalJobs_944_; uint8_t v_wantsRebuild_945_; lean_object* v_failures_946_; lean_object* v_resetCtrl_947_; lean_object* v_lastUpdate_948_; lean_object* v_spinnerIdx_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_986_; 
v_jobs_938_ = lean_ctor_get(v_a_935_, 0);
v___x_939_ = lean_st_ref_take(v_jobs_938_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_942_ = lean_st_ref_set(v_jobs_938_, v___x_941_);
v_jobNo_943_ = lean_ctor_get(v_a_936_, 0);
v_totalJobs_944_ = lean_ctor_get(v_a_936_, 1);
v_wantsRebuild_945_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*6);
v_failures_946_ = lean_ctor_get(v_a_936_, 2);
v_resetCtrl_947_ = lean_ctor_get(v_a_936_, 3);
v_lastUpdate_948_ = lean_ctor_get(v_a_936_, 4);
v_spinnerIdx_949_ = lean_ctor_get(v_a_936_, 5);
v_isSharedCheck_986_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_986_ == 0)
{
v___x_951_ = v_a_936_;
v_isShared_952_ = v_isSharedCheck_986_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_spinnerIdx_949_);
lean_inc(v_lastUpdate_948_);
lean_inc(v_resetCtrl_947_);
lean_inc(v_failures_946_);
lean_inc(v_totalJobs_944_);
lean_inc(v_jobNo_943_);
lean_dec(v_a_936_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_986_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___y_955_; lean_object* v_fst_956_; lean_object* v_snd_957_; lean_object* v___y_967_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_953_ = lean_array_get_size(v___x_939_);
v___x_970_ = lean_nat_add(v_totalJobs_944_, v___x_953_);
lean_dec(v_totalJobs_944_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_970_);
v___x_972_ = v___x_951_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_jobNo_943_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_failures_946_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_resetCtrl_947_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_lastUpdate_948_);
lean_ctor_set(v_reuseFailAlloc_985_, 5, v_spinnerIdx_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*6, v_wantsRebuild_945_);
v___x_972_ = v_reuseFailAlloc_985_;
goto v_reusejp_971_;
}
v___jp_954_:
{
uint8_t v___x_958_; 
v___x_958_ = lean_nat_dec_lt(v___x_940_, v___x_953_);
if (v___x_958_ == 0)
{
lean_dec_ref(v_snd_957_);
lean_dec_ref(v_fst_956_);
lean_dec(v___x_939_);
lean_dec_ref(v_a_935_);
return v___y_955_;
}
else
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_le(v___x_953_, v___x_953_);
if (v___x_959_ == 0)
{
if (v___x_958_ == 0)
{
lean_dec_ref(v_snd_957_);
lean_dec_ref(v_fst_956_);
lean_dec(v___x_939_);
lean_dec_ref(v_a_935_);
return v___y_955_;
}
else
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
lean_dec_ref(v___y_955_);
v___x_960_ = ((size_t)0ULL);
v___x_961_ = lean_usize_of_nat(v___x_953_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v___x_939_, v___x_960_, v___x_961_, v_fst_956_, v_a_935_, v_snd_957_);
lean_dec(v___x_939_);
return v___x_962_;
}
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
lean_dec_ref(v___y_955_);
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_usize_of_nat(v___x_953_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v___x_939_, v___x_963_, v___x_964_, v_fst_956_, v_a_935_, v_snd_957_);
lean_dec(v___x_939_);
return v___x_965_;
}
}
}
v___jp_966_:
{
lean_object* v_fst_968_; lean_object* v_snd_969_; 
v_fst_968_ = lean_ctor_get(v___y_967_, 0);
lean_inc(v_fst_968_);
v_snd_969_ = lean_ctor_get(v___y_967_, 1);
lean_inc(v_snd_969_);
v___y_955_ = v___y_967_;
v_fst_956_ = v_fst_968_;
v_snd_957_ = v_snd_969_;
goto v___jp_954_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0);
v___x_974_ = lean_array_get_size(v_unfinished_934_);
v___x_975_ = lean_nat_dec_lt(v___x_940_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_inc_ref(v___x_972_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_973_);
lean_ctor_set(v___x_976_, 1, v___x_972_);
v___y_955_ = v___x_976_;
v_fst_956_ = v___x_973_;
v_snd_957_ = v___x_972_;
goto v___jp_954_;
}
else
{
uint8_t v___x_977_; 
v___x_977_ = lean_nat_dec_le(v___x_974_, v___x_974_);
if (v___x_977_ == 0)
{
if (v___x_975_ == 0)
{
lean_object* v___x_978_; 
lean_inc_ref(v___x_972_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_973_);
lean_ctor_set(v___x_978_, 1, v___x_972_);
v___y_955_ = v___x_978_;
v_fst_956_ = v___x_973_;
v_snd_957_ = v___x_972_;
goto v___jp_954_;
}
else
{
size_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((size_t)0ULL);
v___x_980_ = lean_usize_of_nat(v___x_974_);
lean_inc_ref(v_a_935_);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v_unfinished_934_, v___x_979_, v___x_980_, v___x_973_, v_a_935_, v___x_972_);
v___y_967_ = v___x_981_;
goto v___jp_966_;
}
}
else
{
size_t v___x_982_; size_t v___x_983_; lean_object* v___x_984_; 
v___x_982_ = ((size_t)0ULL);
v___x_983_ = lean_usize_of_nat(v___x_974_);
lean_inc_ref(v_a_935_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v_unfinished_934_, v___x_982_, v___x_983_, v___x_973_, v_a_935_, v___x_972_);
v___y_967_ = v___x_984_;
goto v___jp_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object* v_unfinished_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lake_Build_Run_0__Lake_Monitor_poll(v_unfinished_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_unfinished_987_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___y_996_; lean_object* v___x_1014_; lean_object* v_lastUpdate_1015_; lean_object* v_updateFrequency_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1014_ = lean_io_mono_ms_now();
v_lastUpdate_1015_ = lean_ctor_get(v_a_993_, 4);
v_updateFrequency_1016_ = lean_ctor_get(v_a_992_, 2);
v___x_1017_ = lean_nat_sub(v___x_1014_, v_lastUpdate_1015_);
lean_dec(v___x_1014_);
v___x_1018_ = lean_nat_sub(v_updateFrequency_1016_, v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_nat_dec_lt(v___x_1019_, v___x_1018_);
if (v___x_1020_ == 0)
{
lean_dec(v___x_1018_);
v___y_996_ = v_a_993_;
goto v___jp_995_;
}
else
{
uint32_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_uint32_of_nat(v___x_1018_);
lean_dec(v___x_1018_);
v___x_1022_ = l_IO_sleep(v___x_1021_);
v___y_996_ = v_a_993_;
goto v___jp_995_;
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v_jobNo_998_; lean_object* v_totalJobs_999_; uint8_t v_wantsRebuild_1000_; lean_object* v_failures_1001_; lean_object* v_resetCtrl_1002_; lean_object* v_spinnerIdx_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1012_; 
v___x_997_ = lean_io_mono_ms_now();
v_jobNo_998_ = lean_ctor_get(v___y_996_, 0);
v_totalJobs_999_ = lean_ctor_get(v___y_996_, 1);
v_wantsRebuild_1000_ = lean_ctor_get_uint8(v___y_996_, sizeof(void*)*6);
v_failures_1001_ = lean_ctor_get(v___y_996_, 2);
v_resetCtrl_1002_ = lean_ctor_get(v___y_996_, 3);
v_spinnerIdx_1003_ = lean_ctor_get(v___y_996_, 5);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___y_996_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___y_996_, 4);
lean_dec(v_unused_1013_);
v___x_1005_ = v___y_996_;
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_spinnerIdx_1003_);
lean_inc(v_resetCtrl_1002_);
lean_inc(v_failures_1001_);
lean_inc(v_totalJobs_999_);
lean_inc(v_jobNo_998_);
lean_dec(v___y_996_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v___x_997_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_jobNo_998_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_totalJobs_999_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_failures_1001_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_resetCtrl_1002_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1011_, 5, v_spinnerIdx_1003_);
lean_ctor_set_uint8(v_reuseFailAlloc_1011_, sizeof(void*)*6, v_wantsRebuild_1000_);
v___x_1009_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1023_, v_a_1024_);
lean_dec_ref(v_a_1023_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_unfinished_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1051_; 
lean_inc_ref(v_a_1028_);
v___x_1031_ = l___private_Lake_Build_Run_0__Lake_Monitor_poll(v_unfinished_1027_, v_a_1028_, v_a_1029_);
lean_dec_ref(v_unfinished_1027_);
v_fst_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_fst_1032_);
v_snd_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1033_);
lean_dec_ref(v___x_1031_);
v_fst_1034_ = lean_ctor_get(v_fst_1032_, 0);
v_snd_1035_ = lean_ctor_get(v_fst_1032_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_fst_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1037_ = v_fst_1032_;
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_fst_1032_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v_snd_1035_);
v___x_1041_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v_snd_1035_);
lean_dec(v_fst_1034_);
lean_dec_ref(v_a_1028_);
v___x_1042_ = lean_box(0);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_snd_1033_);
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_snd_1033_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v___x_1046_; lean_object* v_snd_1047_; lean_object* v___x_1048_; lean_object* v_snd_1049_; 
lean_del_object(v___x_1037_);
lean_inc_ref(v_a_1028_);
v___x_1046_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1034_, v_snd_1035_, v_a_1028_, v_snd_1033_);
lean_dec(v_fst_1034_);
v_snd_1047_ = lean_ctor_get(v___x_1046_, 1);
lean_inc(v_snd_1047_);
lean_dec_ref(v___x_1046_);
v___x_1048_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1028_, v_snd_1047_);
v_snd_1049_ = lean_ctor_get(v___x_1048_, 1);
lean_inc(v_snd_1049_);
lean_dec_ref(v___x_1048_);
v_unfinished_1027_ = v_snd_1035_;
v_a_1029_ = v_snd_1049_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_unfinished_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_unfinished_1052_, v_a_1053_, v_a_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v_snd_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1122_; 
lean_inc_ref(v_a_1058_);
v___x_1061_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_init_1057_, v_a_1058_, v_a_1059_);
v_snd_1062_ = lean_ctor_get(v___x_1061_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1061_, 0);
lean_dec(v_unused_1123_);
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1122_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_snd_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1122_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_jobNo_1066_; lean_object* v_totalJobs_1067_; uint8_t v_wantsRebuild_1068_; lean_object* v_failures_1069_; lean_object* v_resetCtrl_1070_; lean_object* v_lastUpdate_1071_; lean_object* v_spinnerIdx_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1121_; 
v_jobNo_1066_ = lean_ctor_get(v_snd_1062_, 0);
v_totalJobs_1067_ = lean_ctor_get(v_snd_1062_, 1);
v_wantsRebuild_1068_ = lean_ctor_get_uint8(v_snd_1062_, sizeof(void*)*6);
v_failures_1069_ = lean_ctor_get(v_snd_1062_, 2);
v_resetCtrl_1070_ = lean_ctor_get(v_snd_1062_, 3);
v_lastUpdate_1071_ = lean_ctor_get(v_snd_1062_, 4);
v_spinnerIdx_1072_ = lean_ctor_get(v_snd_1062_, 5);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_snd_1062_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1074_ = v_snd_1062_;
v_isShared_1075_ = v_isSharedCheck_1121_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_spinnerIdx_1072_);
lean_inc(v_lastUpdate_1071_);
lean_inc(v_resetCtrl_1070_);
lean_inc(v_failures_1069_);
lean_inc(v_totalJobs_1067_);
lean_inc(v_jobNo_1066_);
lean_dec(v_snd_1062_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1121_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 3, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_jobNo_1066_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_totalJobs_1067_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_failures_1069_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_lastUpdate_1071_);
lean_ctor_set(v_reuseFailAlloc_1120_, 5, v_spinnerIdx_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*6, v_wantsRebuild_1068_);
v___x_1078_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v_val_1080_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_string_utf8_byte_size(v_resetCtrl_1070_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_nat_dec_eq(v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v_out_1087_; lean_object* v_flush_1088_; lean_object* v_putStr_1089_; lean_object* v___x_1094_; 
v_out_1087_ = lean_ctor_get(v_a_1058_, 1);
lean_inc_ref(v_out_1087_);
lean_dec_ref(v_a_1058_);
v_flush_1088_ = lean_ctor_get(v_out_1087_, 0);
lean_inc_ref(v_flush_1088_);
v_putStr_1089_ = lean_ctor_get(v_out_1087_, 4);
lean_inc_ref(v_putStr_1089_);
lean_dec_ref(v_out_1087_);
lean_inc_ref(v_resetCtrl_1070_);
v___x_1094_ = lean_apply_2(v_putStr_1089_, v_resetCtrl_1070_, lean_box(0));
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_resetCtrl_1070_);
goto v___jp_1090_;
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1117_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1117_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1117_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1099_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1100_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1101_ = lean_unsigned_to_nat(89u);
v___x_1102_ = lean_unsigned_to_nat(4u);
v___x_1103_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1104_ = lean_io_error_to_string(v_a_1095_);
v___x_1105_ = lean_string_append(v___x_1103_, v___x_1104_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1107_ = lean_string_append(v___x_1105_, v___x_1106_);
v___x_1108_ = l_String_quote(v_resetCtrl_1070_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 3);
lean_ctor_set(v___x_1097_, 0, v___x_1108_);
v___x_1110_ = v___x_1097_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = l_Std_Format_defWidth;
v___x_1112_ = l_Std_Format_pretty(v___x_1110_, v___x_1111_, v___x_1085_, v___x_1085_);
v___x_1113_ = lean_string_append(v___x_1107_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = l_mkPanicMessageWithDecl(v___x_1099_, v___x_1100_, v___x_1101_, v___x_1102_, v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1114_);
goto v___jp_1090_;
}
}
}
v___jp_1090_:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_apply_1(v_flush_1088_, lean_box(0));
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v_val_1080_ = v_a_1092_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1093_; 
lean_dec_ref(v___x_1091_);
v___x_1093_ = lean_box(0);
v_val_1080_ = v___x_1093_;
goto v___jp_1079_;
}
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v_resetCtrl_1070_);
lean_del_object(v___x_1064_);
lean_dec_ref(v_a_1058_);
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1078_);
return v___x_1119_;
}
v___jp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v___x_1078_);
lean_ctor_set(v___x_1064_, 0, v_val_1080_);
v___x_1082_ = v___x_1064_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_val_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1078_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1124_, v_a_1125_, v_a_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1129_){
_start:
{
lean_object* v_failures_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_failures_1130_ = lean_ctor_get(v_self_1129_, 0);
v___x_1131_ = lean_array_get_size(v_failures_1130_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1134_);
lean_dec_ref(v_self_1134_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1137_, lean_object* v_jobs_1138_){
_start:
{
lean_object* v_toLogConfig_1140_; uint8_t v_verbosity_1141_; uint8_t v_failLv_1142_; uint8_t v_outLv_1143_; uint8_t v_ansiMode_1144_; lean_object* v_out_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; uint8_t v___x_1150_; uint8_t v___y_1152_; uint8_t v___y_1153_; uint8_t v___y_1157_; 
v_toLogConfig_1140_ = lean_ctor_get(v_cfg_1137_, 0);
v_verbosity_1141_ = lean_ctor_get_uint8(v_cfg_1137_, sizeof(void*)*2 + 3);
v_failLv_1142_ = lean_ctor_get_uint8(v_toLogConfig_1140_, sizeof(void*)*1);
v_outLv_1143_ = lean_ctor_get_uint8(v_toLogConfig_1140_, sizeof(void*)*1 + 1);
v_ansiMode_1144_ = lean_ctor_get_uint8(v_toLogConfig_1140_, sizeof(void*)*1 + 2);
v_out_1145_ = lean_ctor_get(v_toLogConfig_1140_, 0);
v___x_1146_ = l_Lake_OutStream_get(v_out_1145_);
lean_inc_ref(v___x_1146_);
v___x_1147_ = l_Lake_AnsiMode_isEnabled(v___x_1146_, v_ansiMode_1144_);
v___x_1148_ = l_Lake_BuildConfig_showProgress(v_cfg_1137_);
v___x_1149_ = 2;
v___x_1150_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1141_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = 2;
v___y_1157_ = v___x_1159_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = 0;
v___y_1157_ = v___x_1160_;
goto v___jp_1156_;
}
v___jp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(100u);
v___x_1155_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v___x_1155_, 0, v_jobs_1138_);
lean_ctor_set(v___x_1155_, 1, v___x_1146_);
lean_ctor_set(v___x_1155_, 2, v___x_1154_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3, v_outLv_1143_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 1, v_failLv_1142_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 2, v___y_1152_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 3, v___x_1150_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 4, v___x_1147_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 5, v___x_1148_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 6, v___y_1153_);
return v___x_1155_;
}
v___jp_1156_:
{
if (v___x_1150_ == 0)
{
if (v___x_1147_ == 0)
{
uint8_t v___x_1158_; 
v___x_1158_ = 1;
v___y_1152_ = v___y_1157_;
v___y_1153_ = v___x_1158_;
goto v___jp_1151_;
}
else
{
v___y_1152_ = v___y_1157_;
v___y_1153_ = v___x_1150_;
goto v___jp_1151_;
}
}
else
{
v___y_1152_ = v___y_1157_;
v___y_1153_ = v___x_1150_;
goto v___jp_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1161_, lean_object* v_jobs_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1161_, v_jobs_1162_);
lean_dec_ref(v_cfg_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1165_, lean_object* v_initJobs_1166_, lean_object* v_initFailures_1167_, lean_object* v_resetCtrl_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_snd_1175_; lean_object* v_totalJobs_1176_; uint8_t v_wantsRebuild_1177_; lean_object* v_failures_1178_; lean_object* v___x_1179_; 
v___x_1170_ = lean_io_mono_ms_now();
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = 0;
v___x_1173_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1171_);
lean_ctor_set(v___x_1173_, 2, v_initFailures_1167_);
lean_ctor_set(v___x_1173_, 3, v_resetCtrl_1168_);
lean_ctor_set(v___x_1173_, 4, v___x_1170_);
lean_ctor_set(v___x_1173_, 5, v___x_1171_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*6, v___x_1172_);
v___x_1174_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1166_, v_ctx_1165_, v___x_1173_);
v_snd_1175_ = lean_ctor_get(v___x_1174_, 1);
lean_inc(v_snd_1175_);
lean_dec_ref(v___x_1174_);
v_totalJobs_1176_ = lean_ctor_get(v_snd_1175_, 1);
lean_inc(v_totalJobs_1176_);
v_wantsRebuild_1177_ = lean_ctor_get_uint8(v_snd_1175_, sizeof(void*)*6);
v_failures_1178_ = lean_ctor_get(v_snd_1175_, 2);
lean_inc_ref(v_failures_1178_);
lean_dec(v_snd_1175_);
v___x_1179_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1179_, 0, v_failures_1178_);
lean_ctor_set(v___x_1179_, 1, v_totalJobs_1176_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*2, v_wantsRebuild_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1180_, lean_object* v_initJobs_1181_, lean_object* v_initFailures_1182_, lean_object* v_resetCtrl_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1180_, v_initJobs_1181_, v_initFailures_1182_, v_resetCtrl_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1186_, lean_object* v_jobs_1187_, lean_object* v_out_1188_, uint8_t v_failLv_1189_, uint8_t v_outLv_1190_, uint8_t v_minAction_1191_, uint8_t v_showOptional_1192_, uint8_t v_useAnsi_1193_, uint8_t v_showProgress_1194_, uint8_t v_showTime_1195_, lean_object* v_resetCtrl_1196_, lean_object* v_initFailures_1197_, lean_object* v_updateFrequency_1198_){
_start:
{
lean_object* v_ctx_1200_; lean_object* v___x_1201_; 
v_ctx_1200_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v_ctx_1200_, 0, v_jobs_1187_);
lean_ctor_set(v_ctx_1200_, 1, v_out_1188_);
lean_ctor_set(v_ctx_1200_, 2, v_updateFrequency_1198_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3, v_outLv_1190_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3 + 1, v_failLv_1189_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3 + 2, v_minAction_1191_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3 + 3, v_showOptional_1192_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3 + 4, v_useAnsi_1193_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3 + 5, v_showProgress_1194_);
lean_ctor_set_uint8(v_ctx_1200_, sizeof(void*)*3 + 6, v_showTime_1195_);
v___x_1201_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1200_, v_initJobs_1186_, v_initFailures_1197_, v_resetCtrl_1196_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1202_, lean_object* v_jobs_1203_, lean_object* v_out_1204_, lean_object* v_failLv_1205_, lean_object* v_outLv_1206_, lean_object* v_minAction_1207_, lean_object* v_showOptional_1208_, lean_object* v_useAnsi_1209_, lean_object* v_showProgress_1210_, lean_object* v_showTime_1211_, lean_object* v_resetCtrl_1212_, lean_object* v_initFailures_1213_, lean_object* v_updateFrequency_1214_, lean_object* v_a_1215_){
_start:
{
uint8_t v_failLv_boxed_1216_; uint8_t v_outLv_boxed_1217_; uint8_t v_minAction_boxed_1218_; uint8_t v_showOptional_boxed_1219_; uint8_t v_useAnsi_boxed_1220_; uint8_t v_showProgress_boxed_1221_; uint8_t v_showTime_boxed_1222_; lean_object* v_res_1223_; 
v_failLv_boxed_1216_ = lean_unbox(v_failLv_1205_);
v_outLv_boxed_1217_ = lean_unbox(v_outLv_1206_);
v_minAction_boxed_1218_ = lean_unbox(v_minAction_1207_);
v_showOptional_boxed_1219_ = lean_unbox(v_showOptional_1208_);
v_useAnsi_boxed_1220_ = lean_unbox(v_useAnsi_1209_);
v_showProgress_boxed_1221_ = lean_unbox(v_showProgress_1210_);
v_showTime_boxed_1222_ = lean_unbox(v_showTime_1211_);
v_res_1223_ = l_Lake_monitorJobs(v_initJobs_1202_, v_jobs_1203_, v_out_1204_, v_failLv_boxed_1216_, v_outLv_boxed_1217_, v_minAction_boxed_1218_, v_showOptional_boxed_1219_, v_useAnsi_boxed_1220_, v_showProgress_boxed_1221_, v_showTime_boxed_1222_, v_resetCtrl_1212_, v_initFailures_1213_, v_updateFrequency_1214_);
return v_res_1223_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1224_; 
v___x_1224_ = 3;
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1225_, lean_object* v_x_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_apply_2(v_logger_1225_, v___y_1227_, lean_box(0));
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1230_, lean_object* v_x_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1230_, v_x_1231_, v___y_1232_);
return v_res_1234_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1239_ = l_String_quote(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Std_Format_defWidth;
v___x_1244_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3);
v___x_1245_ = l_Std_Format_pretty(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1242_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1248_ = l_String_quote(v___x_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = l_Std_Format_defWidth;
v___x_1253_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_1254_ = l_Std_Format_pretty(v___x_1253_, v___x_1252_, v___x_1251_, v___x_1251_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
v___x_1257_ = l_String_quote(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = l_Std_Format_defWidth;
v___x_1262_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_1263_ = l_Std_Format_pretty(v___x_1262_, v___x_1261_, v___x_1260_, v___x_1260_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1265_, lean_object* v_ws_1266_, lean_object* v_out_1267_, lean_object* v_outputsFile_1268_, uint8_t v_isVerbose_1269_){
_start:
{
lean_object* v___f_1273_; lean_object* v___x_1274_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1291_; lean_object* v___y_1292_; uint8_t v___x_1381_; 
lean_inc_ref(v_logger_1265_);
v___f_1273_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1273_, 0, v_logger_1265_);
v___x_1274_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1381_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1266_);
if (v___x_1381_ == 0)
{
lean_object* v_root_1382_; lean_object* v_baseName_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_root_1382_ = lean_ctor_get(v_ws_1266_, 0);
v_baseName_1383_ = lean_ctor_get(v_root_1382_, 1);
lean_inc(v_baseName_1383_);
v___x_1384_ = l_Lean_Name_toString(v_baseName_1383_, v___x_1381_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
v___x_1387_ = 2;
v___x_1388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*1, v___x_1387_);
v___x_1389_ = lean_apply_2(v_logger_1265_, v___x_1388_, lean_box(0));
goto v___jp_1306_;
}
else
{
lean_dec_ref(v_logger_1265_);
goto v___jp_1306_;
}
v___jp_1271_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_box(0);
return v___x_1272_;
}
v___jp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1278_ = lean_array_get_size(v___y_1277_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_nat_dec_lt(v___y_1276_, v___x_1278_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___f_1273_);
return v___x_1279_;
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_le(v___x_1278_, v___x_1278_);
if (v___x_1281_ == 0)
{
if (v___x_1280_ == 0)
{
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___f_1273_);
return v___x_1279_;
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_2380__overap_1284_; lean_object* v___x_1285_; 
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1278_);
v___x_2380__overap_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1274_, v___f_1273_, v___y_1277_, v___x_1282_, v___x_1283_, v___x_1279_);
v___x_1285_ = lean_apply_1(v___x_2380__overap_1284_, lean_box(0));
return v___x_1285_;
}
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_2384__overap_1288_; lean_object* v___x_1289_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1278_);
v___x_2384__overap_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1274_, v___f_1273_, v___y_1277_, v___x_1286_, v___x_1287_, v___x_1279_);
v___x_1289_ = lean_apply_1(v___x_2384__overap_1288_, lean_box(0));
return v___x_1289_;
}
}
}
v___jp_1290_:
{
if (v_isVerbose_1269_ == 0)
{
lean_object* v___x_1293_; 
lean_dec_ref(v___y_1292_);
lean_dec_ref(v___f_1273_);
v___x_1293_ = lean_box(0);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_array_get_size(v___y_1292_);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_nat_dec_lt(v___y_1291_, v___x_1294_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v___y_1292_);
lean_dec_ref(v___f_1273_);
return v___x_1295_;
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_le(v___x_1294_, v___x_1294_);
if (v___x_1297_ == 0)
{
if (v___x_1296_ == 0)
{
lean_dec_ref(v___y_1292_);
lean_dec_ref(v___f_1273_);
return v___x_1295_;
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_2287__overap_1300_; lean_object* v___x_1301_; 
v___x_1298_ = ((size_t)0ULL);
v___x_1299_ = lean_usize_of_nat(v___x_1294_);
v___x_2287__overap_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1274_, v___f_1273_, v___y_1292_, v___x_1298_, v___x_1299_, v___x_1295_);
v___x_1301_ = lean_apply_1(v___x_2287__overap_1300_, lean_box(0));
return v___x_1301_;
}
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_2291__overap_1304_; lean_object* v___x_1305_; 
v___x_1302_ = ((size_t)0ULL);
v___x_1303_ = lean_usize_of_nat(v___x_1294_);
v___x_2291__overap_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1274_, v___f_1273_, v___y_1292_, v___x_1302_, v___x_1303_, v___x_1295_);
v___x_1305_ = lean_apply_1(v___x_2291__overap_1304_, lean_box(0));
return v___x_1305_;
}
}
}
}
v___jp_1306_:
{
lean_object* v_root_1307_; lean_object* v_outputsRef_x3f_1308_; 
v_root_1307_ = lean_ctor_get(v_ws_1266_, 0);
lean_inc_ref(v_root_1307_);
lean_dec_ref(v_ws_1266_);
v_outputsRef_x3f_1308_ = lean_ctor_get(v_root_1307_, 23);
lean_inc(v_outputsRef_x3f_1308_);
lean_dec_ref(v_root_1307_);
if (lean_obj_tag(v_outputsRef_x3f_1308_) == 1)
{
lean_object* v_val_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_val_1309_ = lean_ctor_get(v_outputsRef_x3f_1308_, 0);
lean_inc(v_val_1309_);
lean_dec_ref(v_outputsRef_x3f_1308_);
v___x_1310_ = lean_st_ref_get(v_val_1309_);
lean_dec(v_val_1309_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1313_ = l_Lake_CacheMap_writeFile(v_outputsFile_1268_, v___x_1310_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_array_get_size(v_a_1314_);
v___x_1316_ = lean_nat_dec_eq(v___x_1315_, v___x_1311_);
if (v___x_1316_ == 0)
{
if (v_isVerbose_1269_ == 0)
{
lean_dec(v_a_1314_);
lean_dec_ref(v___f_1273_);
lean_dec_ref(v_out_1267_);
goto v___jp_1271_;
}
else
{
lean_object* v_putStr_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_putStr_1317_ = lean_ctor_get(v_out_1267_, 4);
lean_inc_ref(v_putStr_1317_);
lean_dec_ref(v_out_1267_);
v___x_1318_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1319_ = lean_apply_2(v_putStr_1317_, v___x_1318_, lean_box(0));
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref(v___x_1319_);
v___y_1276_ = v___x_1311_;
v___y_1277_ = v_a_1314_;
goto v___jp_1275_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_2522__overap_1339_; lean_object* v___x_1340_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_1322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1323_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1324_ = lean_unsigned_to_nat(89u);
v___x_1325_ = lean_unsigned_to_nat(4u);
v___x_1326_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1327_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1327_, v_isVerbose_1269_);
v___x_1329_ = lean_string_append(v___x_1326_, v___x_1328_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
v___x_1332_ = lean_io_error_to_string(v_a_1320_);
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1335_ = lean_string_append(v___x_1333_, v___x_1334_);
v___x_1336_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
v___x_1337_ = lean_string_append(v___x_1335_, v___x_1336_);
v___x_1338_ = l_mkPanicMessageWithDecl(v___x_1322_, v___x_1323_, v___x_1324_, v___x_1325_, v___x_1337_);
lean_dec_ref(v___x_1337_);
v___x_2522__overap_1339_ = l_panic___redArg(v___x_1321_, v___x_1338_);
v___x_1340_ = lean_apply_1(v___x_2522__overap_1339_, lean_box(0));
v___y_1276_ = v___x_1311_;
v___y_1277_ = v_a_1314_;
goto v___jp_1275_;
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec_ref(v___f_1273_);
lean_dec_ref(v_out_1267_);
goto v___jp_1271_;
}
}
else
{
lean_object* v_a_1341_; lean_object* v_putStr_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1341_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1313_);
v_putStr_1342_ = lean_ctor_get(v_out_1267_, 4);
lean_inc_ref(v_putStr_1342_);
lean_dec_ref(v_out_1267_);
v___x_1343_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1344_ = lean_apply_2(v_putStr_1342_, v___x_1343_, lean_box(0));
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_dec_ref(v___x_1344_);
v___y_1291_ = v___x_1311_;
v___y_1292_ = v_a_1341_;
goto v___jp_1290_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_2182__overap_1359_; lean_object* v___x_1360_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_1347_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1348_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1349_ = lean_unsigned_to_nat(89u);
v___x_1350_ = lean_unsigned_to_nat(4u);
v___x_1351_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1352_ = lean_io_error_to_string(v_a_1345_);
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = l_mkPanicMessageWithDecl(v___x_1347_, v___x_1348_, v___x_1349_, v___x_1350_, v___x_1357_);
lean_dec_ref(v___x_1357_);
v___x_2182__overap_1359_ = l_panic___redArg(v___x_1346_, v___x_1358_);
v___x_1360_ = lean_apply_1(v___x_2182__overap_1359_, lean_box(0));
v___y_1291_ = v___x_1311_;
v___y_1292_ = v_a_1341_;
goto v___jp_1290_;
}
}
}
else
{
lean_object* v_putStr_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec(v_outputsRef_x3f_1308_);
lean_dec_ref(v___f_1273_);
lean_dec_ref(v_outputsFile_1268_);
v_putStr_1361_ = lean_ctor_get(v_out_1267_, 4);
lean_inc_ref(v_putStr_1361_);
lean_dec_ref(v_out_1267_);
v___x_1362_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
v___x_1363_ = lean_apply_2(v_putStr_1361_, v___x_1362_, lean_box(0));
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
return v_a_1364_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_2337__overap_1379_; lean_object* v___x_1380_; 
v_a_1365_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1363_);
v___x_1366_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_1367_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1368_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1369_ = lean_unsigned_to_nat(89u);
v___x_1370_ = lean_unsigned_to_nat(4u);
v___x_1371_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1372_ = lean_io_error_to_string(v_a_1365_);
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
v___x_1376_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v___x_1378_ = l_mkPanicMessageWithDecl(v___x_1367_, v___x_1368_, v___x_1369_, v___x_1370_, v___x_1377_);
lean_dec_ref(v___x_1377_);
v___x_2337__overap_1379_ = l_panic___redArg(v___x_1366_, v___x_1378_);
v___x_1380_ = lean_apply_1(v___x_2337__overap_1379_, lean_box(0));
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1390_, lean_object* v_ws_1391_, lean_object* v_out_1392_, lean_object* v_outputsFile_1393_, lean_object* v_isVerbose_1394_, lean_object* v_a_1395_){
_start:
{
uint8_t v_isVerbose_boxed_1396_; lean_object* v_res_1397_; 
v_isVerbose_boxed_1396_ = lean_unbox(v_isVerbose_1394_);
v_res_1397_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1390_, v_ws_1391_, v_out_1392_, v_outputsFile_1393_, v_isVerbose_boxed_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1399_, lean_object* v_as_1400_, size_t v_i_1401_, size_t v_stop_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v_val_1406_; uint8_t v___x_1410_; 
v___x_1410_ = lean_usize_dec_eq(v_i_1401_, v_stop_1402_);
if (v___x_1410_ == 0)
{
lean_object* v_putStr_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_putStr_1411_ = lean_ctor_get(v_out_1399_, 4);
v___x_1412_ = lean_array_uget_borrowed(v_as_1400_, v_i_1401_);
v___x_1413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1414_ = lean_string_append(v___x_1413_, v___x_1412_);
v___x_1415_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1416_ = lean_string_append(v___x_1414_, v___x_1415_);
lean_inc_ref(v_putStr_1411_);
lean_inc_ref(v___x_1416_);
v___x_1417_ = lean_apply_2(v_putStr_1411_, v___x_1416_, lean_box(0));
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; 
lean_dec_ref(v___x_1416_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v_val_1406_ = v_a_1418_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1442_; 
v_a_1419_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1421_ = v___x_1417_;
v_isShared_1422_ = v_isSharedCheck_1442_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1417_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1442_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1423_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1424_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1425_ = lean_unsigned_to_nat(89u);
v___x_1426_ = lean_unsigned_to_nat(4u);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1429_ = lean_io_error_to_string(v_a_1419_);
v___x_1430_ = lean_string_append(v___x_1428_, v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1432_ = lean_string_append(v___x_1430_, v___x_1431_);
v___x_1433_ = l_String_quote(v___x_1416_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 3);
lean_ctor_set(v___x_1421_, 0, v___x_1433_);
v___x_1435_ = v___x_1421_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = l_Std_Format_defWidth;
v___x_1437_ = l_Std_Format_pretty(v___x_1435_, v___x_1436_, v___x_1427_, v___x_1427_);
v___x_1438_ = lean_string_append(v___x_1432_, v___x_1437_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = l_mkPanicMessageWithDecl(v___x_1423_, v___x_1424_, v___x_1425_, v___x_1426_, v___x_1438_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1439_);
v_val_1406_ = v___x_1440_;
goto v___jp_1405_;
}
}
}
}
else
{
lean_dec_ref(v_out_1399_);
return v_b_1403_;
}
v___jp_1405_:
{
size_t v___x_1407_; size_t v___x_1408_; 
v___x_1407_ = ((size_t)1ULL);
v___x_1408_ = lean_usize_add(v_i_1401_, v___x_1407_);
v_i_1401_ = v___x_1408_;
v_b_1403_ = v_val_1406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1443_, lean_object* v_as_1444_, lean_object* v_i_1445_, lean_object* v_stop_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_){
_start:
{
size_t v_i_boxed_1449_; size_t v_stop_boxed_1450_; lean_object* v_res_1451_; 
v_i_boxed_1449_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_stop_boxed_1450_ = lean_unbox_usize(v_stop_1446_);
lean_dec(v_stop_1446_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1443_, v_as_1444_, v_i_boxed_1449_, v_stop_boxed_1450_, v_b_1447_);
lean_dec_ref(v_as_1444_);
return v_res_1451_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1459_ = l_String_quote(v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = l_Std_Format_defWidth;
v___x_1464_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1465_ = l_Std_Format_pretty(v___x_1464_, v___x_1463_, v___x_1462_, v___x_1462_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1466_, lean_object* v_out_1467_, lean_object* v_result_1468_){
_start:
{
uint8_t v___y_1471_; lean_object* v___y_1472_; lean_object* v_failures_1546_; lean_object* v_numJobs_1547_; uint8_t v___y_1549_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_failures_1546_ = lean_ctor_get(v_result_1468_, 0);
lean_inc_ref(v_failures_1546_);
v_numJobs_1547_ = lean_ctor_get(v_result_1468_, 1);
lean_inc(v_numJobs_1547_);
lean_dec_ref(v_result_1468_);
v___x_1557_ = lean_array_get_size(v_failures_1546_);
v___x_1558_ = lean_unsigned_to_nat(0u);
v___x_1559_ = lean_nat_dec_eq(v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v_flush_1560_; lean_object* v_putStr_1561_; lean_object* v___y_1567_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_numJobs_1547_);
v_flush_1560_ = lean_ctor_get(v_out_1467_, 0);
lean_inc_ref(v_flush_1560_);
v_putStr_1561_ = lean_ctor_get(v_out_1467_, 4);
v___x_1578_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
lean_inc_ref(v_putStr_1561_);
v___x_1579_ = lean_apply_2(v_putStr_1561_, v___x_1578_, lean_box(0));
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref(v___x_1579_);
goto v___jp_1568_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1582_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1583_ = lean_unsigned_to_nat(89u);
v___x_1584_ = lean_unsigned_to_nat(4u);
v___x_1585_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1586_ = lean_io_error_to_string(v_a_1580_);
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
v___x_1592_ = l_mkPanicMessageWithDecl(v___x_1581_, v___x_1582_, v___x_1583_, v___x_1584_, v___x_1591_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1592_);
goto v___jp_1568_;
}
v___jp_1562_:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_apply_1(v_flush_1560_, lean_box(0));
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1563_);
return v_a_1564_;
}
else
{
lean_object* v___x_1565_; 
lean_dec_ref(v___x_1563_);
v___x_1565_ = lean_box(0);
return v___x_1565_;
}
}
v___jp_1566_:
{
goto v___jp_1562_;
}
v___jp_1568_:
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_nat_dec_lt(v___x_1558_, v___x_1557_);
if (v___x_1569_ == 0)
{
lean_dec_ref(v_failures_1546_);
lean_dec_ref(v_out_1467_);
goto v___jp_1562_;
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_nat_dec_le(v___x_1557_, v___x_1557_);
if (v___x_1571_ == 0)
{
if (v___x_1569_ == 0)
{
lean_dec_ref(v_failures_1546_);
lean_dec_ref(v_out_1467_);
goto v___jp_1562_;
}
else
{
size_t v___x_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((size_t)0ULL);
v___x_1573_ = lean_usize_of_nat(v___x_1557_);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1467_, v_failures_1546_, v___x_1572_, v___x_1573_, v___x_1570_);
lean_dec_ref(v_failures_1546_);
v___y_1567_ = v___x_1574_;
goto v___jp_1566_;
}
}
else
{
size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = lean_usize_of_nat(v___x_1557_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1467_, v_failures_1546_, v___x_1575_, v___x_1576_, v___x_1570_);
lean_dec_ref(v_failures_1546_);
v___y_1567_ = v___x_1577_;
goto v___jp_1566_;
}
}
}
}
else
{
uint8_t v___x_1594_; 
lean_dec_ref(v_failures_1546_);
v___x_1594_ = l_Lake_BuildConfig_showProgress(v_cfg_1466_);
if (v___x_1594_ == 0)
{
v___y_1549_ = v___x_1594_;
goto v___jp_1548_;
}
else
{
uint8_t v_showSuccess_1595_; 
v_showSuccess_1595_ = lean_ctor_get_uint8(v_cfg_1466_, sizeof(void*)*2 + 4);
v___y_1549_ = v_showSuccess_1595_;
goto v___jp_1548_;
}
}
v___jp_1470_:
{
uint8_t v_noBuild_1473_; 
v_noBuild_1473_ = lean_ctor_get_uint8(v_cfg_1466_, sizeof(void*)*2 + 2);
if (v_noBuild_1473_ == 0)
{
lean_object* v_putStr_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_putStr_1474_ = lean_ctor_get(v_out_1467_, 4);
lean_inc_ref(v_putStr_1474_);
lean_dec_ref(v_out_1467_);
v___x_1475_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1476_ = lean_string_append(v___x_1475_, v___y_1472_);
lean_dec_ref(v___y_1472_);
v___x_1477_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
lean_inc_ref(v___x_1478_);
v___x_1479_ = lean_apply_2(v_putStr_1474_, v___x_1478_, lean_box(0));
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; 
lean_dec_ref(v___x_1478_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
return v_a_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1509_; 
v_a_1481_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1483_ = v___x_1479_;
v_isShared_1484_ = v_isSharedCheck_1509_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1479_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1509_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1485_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1486_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1487_ = lean_unsigned_to_nat(89u);
v___x_1488_ = lean_unsigned_to_nat(4u);
v___x_1489_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1491_, v___y_1471_);
v___x_1493_ = lean_string_append(v___x_1489_, v___x_1492_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1495_ = lean_string_append(v___x_1493_, v___x_1494_);
v___x_1496_ = lean_io_error_to_string(v_a_1481_);
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1499_ = lean_string_append(v___x_1497_, v___x_1498_);
v___x_1500_ = l_String_quote(v___x_1478_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set_tag(v___x_1483_, 3);
lean_ctor_set(v___x_1483_, 0, v___x_1500_);
v___x_1502_ = v___x_1483_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1503_ = l_Std_Format_defWidth;
v___x_1504_ = l_Std_Format_pretty(v___x_1502_, v___x_1503_, v___x_1490_, v___x_1490_);
v___x_1505_ = lean_string_append(v___x_1499_, v___x_1504_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = l_mkPanicMessageWithDecl(v___x_1485_, v___x_1486_, v___x_1487_, v___x_1488_, v___x_1505_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1506_);
return v___x_1507_;
}
}
}
}
else
{
lean_object* v_putStr_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_putStr_1510_ = lean_ctor_get(v_out_1467_, 4);
lean_inc_ref(v_putStr_1510_);
lean_dec_ref(v_out_1467_);
v___x_1511_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1512_ = lean_string_append(v___x_1511_, v___y_1472_);
lean_dec_ref(v___y_1472_);
v___x_1513_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1514_ = lean_string_append(v___x_1512_, v___x_1513_);
lean_inc_ref(v___x_1514_);
v___x_1515_ = lean_apply_2(v_putStr_1510_, v___x_1514_, lean_box(0));
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; 
lean_dec_ref(v___x_1514_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
return v_a_1516_;
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1545_; 
v_a_1517_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1519_ = v___x_1515_;
v_isShared_1520_ = v_isSharedCheck_1545_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1515_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1545_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1521_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1522_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1523_ = lean_unsigned_to_nat(89u);
v___x_1524_ = lean_unsigned_to_nat(4u);
v___x_1525_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1527_, v_noBuild_1473_);
v___x_1529_ = lean_string_append(v___x_1525_, v___x_1528_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1531_ = lean_string_append(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_io_error_to_string(v_a_1517_);
v___x_1533_ = lean_string_append(v___x_1531_, v___x_1532_);
lean_dec_ref(v___x_1532_);
v___x_1534_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1535_ = lean_string_append(v___x_1533_, v___x_1534_);
v___x_1536_ = l_String_quote(v___x_1514_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 3);
lean_ctor_set(v___x_1519_, 0, v___x_1536_);
v___x_1538_ = v___x_1519_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1539_ = l_Std_Format_defWidth;
v___x_1540_ = l_Std_Format_pretty(v___x_1538_, v___x_1539_, v___x_1526_, v___x_1526_);
v___x_1541_ = lean_string_append(v___x_1535_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = l_mkPanicMessageWithDecl(v___x_1521_, v___x_1522_, v___x_1523_, v___x_1524_, v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1542_);
return v___x_1543_;
}
}
}
}
}
v___jp_1548_:
{
if (v___y_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_dec(v_numJobs_1547_);
lean_dec_ref(v_out_1467_);
v___x_1550_ = lean_box(0);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_dec_eq(v_numJobs_1547_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = l_Nat_reprFast(v_numJobs_1547_);
v___x_1554_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1555_ = lean_string_append(v___x_1553_, v___x_1554_);
v___y_1471_ = v___y_1549_;
v___y_1472_ = v___x_1555_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1556_; 
lean_dec(v_numJobs_1547_);
v___x_1556_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1471_ = v___y_1549_;
v___y_1472_ = v___x_1556_;
goto v___jp_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1596_, lean_object* v_out_1597_, lean_object* v_result_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1596_, v_out_1597_, v_result_1598_);
lean_dec_ref(v_cfg_1596_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1601_){
_start:
{
lean_object* v_toMonitorResult_1602_; 
v_toMonitorResult_1602_ = lean_ctor_get(v_self_1601_, 0);
lean_inc_ref(v_toMonitorResult_1602_);
return v_toMonitorResult_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1603_);
lean_dec_ref(v_self_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1606_){
_start:
{
lean_object* v___f_1607_; 
v___f_1607_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1607_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1608_){
_start:
{
lean_object* v_out_1609_; 
v_out_1609_ = lean_ctor_get(v_self_1608_, 1);
if (lean_obj_tag(v_out_1609_) == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = 0;
return v___x_1610_;
}
else
{
uint8_t v___x_1611_; 
v___x_1611_ = 1;
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1612_){
_start:
{
uint8_t v_res_1613_; lean_object* v_r_1614_; 
v_res_1613_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1612_);
lean_dec_ref(v_self_1612_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1615_, lean_object* v_self_1616_){
_start:
{
lean_object* v_out_1617_; 
v_out_1617_ = lean_ctor_get(v_self_1616_, 1);
if (lean_obj_tag(v_out_1617_) == 0)
{
uint8_t v___x_1618_; 
v___x_1618_ = 0;
return v___x_1618_;
}
else
{
uint8_t v___x_1619_; 
v___x_1619_ = 1;
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1620_, lean_object* v_self_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1620_, v_self_1621_);
lean_dec_ref(v_self_1621_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1632_, lean_object* v_job_1633_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_failures_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
lean_inc_ref(v_job_1633_);
v___x_1635_ = l_Lake_Job_toOpaque___redArg(v_job_1633_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_mk_empty_array_with_capacity(v___x_1636_);
v___x_1638_ = lean_array_push(v___x_1637_, v___x_1635_);
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1641_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1642_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1632_, v___x_1638_, v___x_1640_, v___x_1641_);
v_failures_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc_ref(v_failures_1643_);
v___x_1644_ = lean_array_get_size(v_failures_1643_);
lean_dec_ref(v_failures_1643_);
v___x_1645_ = lean_nat_dec_eq(v___x_1644_, v___x_1639_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref(v_job_1633_);
v___x_1646_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1642_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
return v___x_1647_;
}
else
{
lean_object* v_task_1648_; lean_object* v___x_1649_; 
v_task_1648_ = lean_ctor_get(v_job_1633_, 0);
lean_inc_ref(v_task_1648_);
lean_dec_ref(v_job_1633_);
v___x_1649_ = lean_io_wait(v_task_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1649_, 1);
lean_dec(v_unused_1659_);
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v___x_1654_);
lean_ctor_set(v___x_1652_, 0, v___x_1642_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1667_; 
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; 
v_unused_1668_ = lean_ctor_get(v___x_1649_, 1);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v___x_1649_, 0);
lean_dec(v_unused_1669_);
v___x_1661_ = v___x_1649_;
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
else
{
lean_dec(v___x_1649_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 0);
lean_ctor_set(v___x_1661_, 1, v___x_1663_);
lean_ctor_set(v___x_1661_, 0, v___x_1642_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1670_, lean_object* v_job_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1670_, v_job_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1674_, lean_object* v_ctx_1675_, lean_object* v_job_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1675_, v_job_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_ctx_1680_, lean_object* v_job_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1679_, v_ctx_1680_, v_job_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* v_ws_1686_, lean_object* v_cfg_1687_, lean_object* v_jobs_1688_){
_start:
{
lean_object* v_lakeEnv_1689_; lean_object* v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_lakeEnv_1689_ = lean_ctor_get(v_ws_1686_, 1);
v___x_1690_ = l_Lake_Env_leanGithash(v_lakeEnv_1689_);
v___x_1691_ = l_Lake_Hash_nil;
v___x_1692_ = lean_string_hash(v___x_1690_);
v___x_1693_ = lean_uint64_mix_hash(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_1695_ = lean_string_append(v___x_1694_, v___x_1690_);
lean_dec_ref(v___x_1690_);
v___x_1696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
v___x_1697_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_1698_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1698_, 0, v___x_1695_);
lean_ctor_set(v___x_1698_, 1, v___x_1696_);
lean_ctor_set(v___x_1698_, 2, v___x_1697_);
lean_ctor_set_uint64(v___x_1698_, sizeof(void*)*3, v___x_1693_);
v___x_1699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1699_, 0, v_cfg_1687_);
lean_ctor_set(v___x_1699_, 1, v_ws_1686_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
lean_ctor_set(v___x_1699_, 3, v_jobs_1688_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_log_1708_; uint8_t v_action_1709_; uint8_t v_wantsRebuild_1710_; lean_object* v_trace_1711_; lean_object* v_buildTime_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1741_; 
v_log_1708_ = lean_ctor_get(v___y_1706_, 0);
v_action_1709_ = lean_ctor_get_uint8(v___y_1706_, sizeof(void*)*3);
v_wantsRebuild_1710_ = lean_ctor_get_uint8(v___y_1706_, sizeof(void*)*3 + 1);
v_trace_1711_ = lean_ctor_get(v___y_1706_, 1);
v_buildTime_1712_ = lean_ctor_get(v___y_1706_, 2);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___y_1706_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1714_ = v___y_1706_;
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_buildTime_1712_);
lean_inc(v_trace_1711_);
lean_inc(v_log_1708_);
lean_dec(v___y_1706_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_apply_7(v_build_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v_log_1708_, lean_box(0));
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1728_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_a_1718_ = lean_ctor_get(v___x_1716_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1720_ = v___x_1716_;
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1728_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v_a_1718_);
v___x_1723_ = v___x_1714_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1718_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_trace_1711_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_buildTime_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, sizeof(void*)*3, v_action_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1727_, sizeof(void*)*3 + 1, v_wantsRebuild_1710_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1717_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1740_; 
v_a_1729_ = lean_ctor_get(v___x_1716_, 0);
v_a_1730_ = lean_ctor_get(v___x_1716_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1732_ = v___x_1716_;
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_inc(v_a_1729_);
lean_dec(v___x_1716_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v_a_1730_);
v___x_1735_ = v___x_1714_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1730_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_trace_1711_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_buildTime_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*3, v_action_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*3 + 1, v_wantsRebuild_1710_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1735_);
v___x_1737_ = v___x_1732_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1729_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_ws_1752_, lean_object* v_cfg_1753_, lean_object* v_jobs_1754_, lean_object* v_build_1755_, lean_object* v_caption_1756_){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v_bctx_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1758_ = lean_box(1);
v___x_1759_ = lean_st_mk_ref(v___x_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1760_, 0, v_build_1755_);
v___x_1761_ = lean_box(0);
v_bctx_1762_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_1752_, v_cfg_1753_, v_jobs_1754_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_box(0);
v___x_1766_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
lean_inc(v___x_1759_);
v___x_1767_ = l_Lake_Job_async___redArg(v___x_1761_, v___f_1760_, v___x_1763_, v_caption_1756_, v___x_1766_, v___x_1765_, v___x_1764_, v___x_1759_, v_bctx_1762_);
v___x_1768_ = lean_st_ref_get(v___x_1759_);
lean_dec(v___x_1759_);
lean_dec(v___x_1768_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_ws_1769_, lean_object* v_cfg_1770_, lean_object* v_jobs_1771_, lean_object* v_build_1772_, lean_object* v_caption_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_ws_1769_, v_cfg_1770_, v_jobs_1771_, v_build_1772_, v_caption_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_1776_, lean_object* v_ws_1777_, lean_object* v_cfg_1778_, lean_object* v_jobs_1779_, lean_object* v_build_1780_, lean_object* v_caption_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_ws_1777_, v_cfg_1778_, v_jobs_1779_, v_build_1780_, v_caption_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_1784_, lean_object* v_ws_1785_, lean_object* v_cfg_1786_, lean_object* v_jobs_1787_, lean_object* v_build_1788_, lean_object* v_caption_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_1784_, v_ws_1785_, v_cfg_1786_, v_jobs_1787_, v_build_1788_, v_caption_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(lean_object* v___x_1792_, uint8_t v___x_1793_, uint8_t v___x_1794_, lean_object* v_as_1795_, size_t v_i_1796_, size_t v_stop_1797_, lean_object* v_b_1798_){
_start:
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_usize_dec_eq(v_i_1796_, v_stop_1797_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; 
v___x_1801_ = lean_array_uget_borrowed(v_as_1795_, v_i_1796_);
lean_inc_ref(v___x_1792_);
v___x_1802_ = l_Lake_logToStream(v___x_1801_, v___x_1792_, v___x_1793_, v___x_1794_);
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1796_, v___x_1803_);
v_i_1796_ = v___x_1804_;
v_b_1798_ = v___x_1802_;
goto _start;
}
else
{
lean_dec_ref(v___x_1792_);
return v_b_1798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0___boxed(lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v___x_1808_, lean_object* v_as_1809_, lean_object* v_i_1810_, lean_object* v_stop_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v___x_1211__boxed_1814_; uint8_t v___x_1212__boxed_1815_; size_t v_i_boxed_1816_; size_t v_stop_boxed_1817_; lean_object* v_res_1818_; 
v___x_1211__boxed_1814_ = lean_unbox(v___x_1807_);
v___x_1212__boxed_1815_ = lean_unbox(v___x_1808_);
v_i_boxed_1816_ = lean_unbox_usize(v_i_1810_);
lean_dec(v_i_1810_);
v_stop_boxed_1817_ = lean_unbox_usize(v_stop_1811_);
lean_dec(v_stop_1811_);
v_res_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(v___x_1806_, v___x_1211__boxed_1814_, v___x_1212__boxed_1815_, v_as_1809_, v_i_boxed_1816_, v_stop_boxed_1817_, v_b_1812_);
lean_dec_ref(v_as_1809_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(lean_object* v___x_1819_, uint8_t v___x_1820_, uint8_t v___x_1821_, lean_object* v_ws_1822_, lean_object* v_out_1823_, lean_object* v_outputsFile_1824_, uint8_t v_isVerbose_1825_){
_start:
{
lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1843_; lean_object* v___y_1844_; uint8_t v___x_1925_; 
v___x_1925_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1822_);
if (v___x_1925_ == 0)
{
lean_object* v_root_1926_; lean_object* v_baseName_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_root_1926_ = lean_ctor_get(v_ws_1822_, 0);
v_baseName_1927_ = lean_ctor_get(v_root_1926_, 1);
lean_inc(v_baseName_1927_);
v___x_1928_ = l_Lean_Name_toString(v_baseName_1927_, v___x_1925_);
v___x_1929_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
v___x_1931_ = 2;
v___x_1932_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*1, v___x_1931_);
lean_inc_ref(v___x_1819_);
v___x_1933_ = l_Lake_logToStream(v___x_1932_, v___x_1819_, v___x_1820_, v___x_1821_);
lean_dec_ref(v___x_1932_);
goto v___jp_1856_;
}
else
{
goto v___jp_1856_;
}
v___jp_1827_:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_box(0);
return v___x_1828_;
}
v___jp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1832_ = lean_array_get_size(v___y_1830_);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_nat_dec_lt(v___y_1831_, v___x_1832_);
if (v___x_1834_ == 0)
{
lean_dec_ref(v___y_1830_);
lean_dec_ref(v___x_1819_);
return v___x_1833_;
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_nat_dec_le(v___x_1832_, v___x_1832_);
if (v___x_1835_ == 0)
{
if (v___x_1834_ == 0)
{
lean_dec_ref(v___y_1830_);
lean_dec_ref(v___x_1819_);
return v___x_1833_;
}
else
{
size_t v___x_1836_; size_t v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = lean_usize_of_nat(v___x_1832_);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(v___x_1819_, v___x_1820_, v___x_1821_, v___y_1830_, v___x_1836_, v___x_1837_, v___x_1833_);
lean_dec_ref(v___y_1830_);
return v___x_1838_;
}
}
else
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = lean_usize_of_nat(v___x_1832_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(v___x_1819_, v___x_1820_, v___x_1821_, v___y_1830_, v___x_1839_, v___x_1840_, v___x_1833_);
lean_dec_ref(v___y_1830_);
return v___x_1841_;
}
}
}
v___jp_1842_:
{
if (v_isVerbose_1825_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___x_1819_);
v___x_1845_ = lean_box(0);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = lean_array_get_size(v___y_1843_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_nat_dec_lt(v___y_1844_, v___x_1846_);
if (v___x_1848_ == 0)
{
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___x_1819_);
return v___x_1847_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_le(v___x_1846_, v___x_1846_);
if (v___x_1849_ == 0)
{
if (v___x_1848_ == 0)
{
lean_dec_ref(v___y_1843_);
lean_dec_ref(v___x_1819_);
return v___x_1847_;
}
else
{
size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = lean_usize_of_nat(v___x_1846_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(v___x_1819_, v___x_1820_, v___x_1821_, v___y_1843_, v___x_1850_, v___x_1851_, v___x_1847_);
lean_dec_ref(v___y_1843_);
return v___x_1852_;
}
}
else
{
size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((size_t)0ULL);
v___x_1854_ = lean_usize_of_nat(v___x_1846_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(v___x_1819_, v___x_1820_, v___x_1821_, v___y_1843_, v___x_1853_, v___x_1854_, v___x_1847_);
lean_dec_ref(v___y_1843_);
return v___x_1855_;
}
}
}
}
v___jp_1856_:
{
lean_object* v_root_1857_; lean_object* v_outputsRef_x3f_1858_; 
v_root_1857_ = lean_ctor_get(v_ws_1822_, 0);
lean_inc_ref(v_root_1857_);
lean_dec_ref(v_ws_1822_);
v_outputsRef_x3f_1858_ = lean_ctor_get(v_root_1857_, 23);
lean_inc(v_outputsRef_x3f_1858_);
lean_dec_ref(v_root_1857_);
if (lean_obj_tag(v_outputsRef_x3f_1858_) == 1)
{
lean_object* v_val_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_val_1859_ = lean_ctor_get(v_outputsRef_x3f_1858_, 0);
lean_inc(v_val_1859_);
lean_dec_ref(v_outputsRef_x3f_1858_);
v___x_1860_ = lean_st_ref_get(v_val_1859_);
lean_dec(v_val_1859_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1863_ = l_Lake_CacheMap_writeFile(v_outputsFile_1824_, v___x_1860_, v___x_1862_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = lean_array_get_size(v_a_1864_);
v___x_1866_ = lean_nat_dec_eq(v___x_1865_, v___x_1861_);
if (v___x_1866_ == 0)
{
if (v_isVerbose_1825_ == 0)
{
lean_dec(v_a_1864_);
lean_dec_ref(v_out_1823_);
lean_dec_ref(v___x_1819_);
goto v___jp_1827_;
}
else
{
lean_object* v_putStr_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_putStr_1867_ = lean_ctor_get(v_out_1823_, 4);
lean_inc_ref(v_putStr_1867_);
lean_dec_ref(v_out_1823_);
v___x_1868_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1869_ = lean_apply_2(v_putStr_1867_, v___x_1868_, lean_box(0));
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec_ref(v___x_1869_);
v___y_1830_ = v_a_1864_;
v___y_1831_ = v___x_1861_;
goto v___jp_1829_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1869_);
v___x_1871_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1872_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1873_ = lean_unsigned_to_nat(89u);
v___x_1874_ = lean_unsigned_to_nat(4u);
v___x_1875_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1876_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1877_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1876_, v_isVerbose_1825_);
v___x_1878_ = lean_string_append(v___x_1875_, v___x_1877_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1880_ = lean_string_append(v___x_1878_, v___x_1879_);
v___x_1881_ = lean_io_error_to_string(v_a_1870_);
v___x_1882_ = lean_string_append(v___x_1880_, v___x_1881_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1884_ = lean_string_append(v___x_1882_, v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
v___x_1886_ = lean_string_append(v___x_1884_, v___x_1885_);
v___x_1887_ = l_mkPanicMessageWithDecl(v___x_1871_, v___x_1872_, v___x_1873_, v___x_1874_, v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1887_);
v___y_1830_ = v_a_1864_;
v___y_1831_ = v___x_1861_;
goto v___jp_1829_;
}
}
}
else
{
lean_dec(v_a_1864_);
lean_dec_ref(v_out_1823_);
lean_dec_ref(v___x_1819_);
goto v___jp_1827_;
}
}
else
{
lean_object* v_a_1889_; lean_object* v_putStr_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1889_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1863_);
v_putStr_1890_ = lean_ctor_get(v_out_1823_, 4);
lean_inc_ref(v_putStr_1890_);
lean_dec_ref(v_out_1823_);
v___x_1891_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1892_ = lean_apply_2(v_putStr_1890_, v___x_1891_, lean_box(0));
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_dec_ref(v___x_1892_);
v___y_1843_ = v_a_1889_;
v___y_1844_ = v___x_1861_;
goto v___jp_1842_;
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1895_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1896_ = lean_unsigned_to_nat(89u);
v___x_1897_ = lean_unsigned_to_nat(4u);
v___x_1898_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1899_ = lean_io_error_to_string(v_a_1893_);
v___x_1900_ = lean_string_append(v___x_1898_, v___x_1899_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1902_ = lean_string_append(v___x_1900_, v___x_1901_);
v___x_1903_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
v___x_1904_ = lean_string_append(v___x_1902_, v___x_1903_);
v___x_1905_ = l_mkPanicMessageWithDecl(v___x_1894_, v___x_1895_, v___x_1896_, v___x_1897_, v___x_1904_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1905_);
v___y_1843_ = v_a_1889_;
v___y_1844_ = v___x_1861_;
goto v___jp_1842_;
}
}
}
else
{
lean_object* v_putStr_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_outputsRef_x3f_1858_);
lean_dec_ref(v_outputsFile_1824_);
lean_dec_ref(v___x_1819_);
v_putStr_1907_ = lean_ctor_get(v_out_1823_, 4);
lean_inc_ref(v_putStr_1907_);
lean_dec_ref(v_out_1823_);
v___x_1908_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
v___x_1909_ = lean_apply_2(v_putStr_1907_, v___x_1908_, lean_box(0));
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___x_1909_);
return v_a_1910_;
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1911_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1909_);
v___x_1912_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1913_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1914_ = lean_unsigned_to_nat(89u);
v___x_1915_ = lean_unsigned_to_nat(4u);
v___x_1916_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1917_ = lean_io_error_to_string(v_a_1911_);
v___x_1918_ = lean_string_append(v___x_1916_, v___x_1917_);
lean_dec_ref(v___x_1917_);
v___x_1919_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1920_ = lean_string_append(v___x_1918_, v___x_1919_);
v___x_1921_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
v___x_1922_ = lean_string_append(v___x_1920_, v___x_1921_);
v___x_1923_ = l_mkPanicMessageWithDecl(v___x_1912_, v___x_1913_, v___x_1914_, v___x_1915_, v___x_1922_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1923_);
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0___boxed(lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v___x_1936_, lean_object* v_ws_1937_, lean_object* v_out_1938_, lean_object* v_outputsFile_1939_, lean_object* v_isVerbose_1940_, lean_object* v_a_1941_){
_start:
{
uint8_t v___x_1379__boxed_1942_; uint8_t v___x_1380__boxed_1943_; uint8_t v_isVerbose_boxed_1944_; lean_object* v_res_1945_; 
v___x_1379__boxed_1942_ = lean_unbox(v___x_1935_);
v___x_1380__boxed_1943_ = lean_unbox(v___x_1936_);
v_isVerbose_boxed_1944_ = lean_unbox(v_isVerbose_1940_);
v_res_1945_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(v___x_1934_, v___x_1379__boxed_1942_, v___x_1380__boxed_1943_, v_ws_1937_, v_out_1938_, v_outputsFile_1939_, v_isVerbose_boxed_1944_);
return v_res_1945_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = 3;
v___x_1947_ = lean_uint32_to_uint8(v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(lean_object* v_ws_1948_, lean_object* v_cfg_1949_, lean_object* v_ctx_1950_, lean_object* v_result_1951_){
_start:
{
lean_object* v___y_1954_; lean_object* v_out_1957_; uint8_t v_outLv_1958_; uint8_t v_useAnsi_1959_; lean_object* v_toMonitorResult_1960_; lean_object* v_out_1961_; lean_object* v___x_1962_; uint8_t v_noBuild_1963_; uint8_t v_verbosity_1964_; lean_object* v_outputsFile_x3f_1965_; 
v_out_1957_ = lean_ctor_get(v_ctx_1950_, 1);
lean_inc_ref(v_out_1957_);
v_outLv_1958_ = lean_ctor_get_uint8(v_ctx_1950_, sizeof(void*)*3);
v_useAnsi_1959_ = lean_ctor_get_uint8(v_ctx_1950_, sizeof(void*)*3 + 4);
lean_dec_ref(v_ctx_1950_);
v_toMonitorResult_1960_ = lean_ctor_get(v_result_1951_, 0);
lean_inc_ref(v_toMonitorResult_1960_);
v_out_1961_ = lean_ctor_get(v_result_1951_, 1);
lean_inc_ref(v_out_1961_);
lean_dec_ref(v_result_1951_);
lean_inc_ref(v_toMonitorResult_1960_);
lean_inc_ref(v_out_1957_);
v___x_1962_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1949_, v_out_1957_, v_toMonitorResult_1960_);
v_noBuild_1963_ = lean_ctor_get_uint8(v_cfg_1949_, sizeof(void*)*2 + 2);
v_verbosity_1964_ = lean_ctor_get_uint8(v_cfg_1949_, sizeof(void*)*2 + 3);
v_outputsFile_x3f_1965_ = lean_ctor_get(v_cfg_1949_, 1);
lean_inc(v_outputsFile_x3f_1965_);
lean_dec_ref(v_cfg_1949_);
if (lean_obj_tag(v_outputsFile_x3f_1965_) == 1)
{
lean_object* v_val_1980_; uint8_t v___y_1982_; 
v_val_1980_ = lean_ctor_get(v_outputsFile_x3f_1965_, 0);
lean_inc(v_val_1980_);
lean_dec_ref(v_outputsFile_x3f_1965_);
if (v_verbosity_1964_ == 2)
{
uint8_t v___x_1984_; 
v___x_1984_ = 1;
v___y_1982_ = v___x_1984_;
goto v___jp_1981_;
}
else
{
uint8_t v___x_1985_; 
v___x_1985_ = 0;
v___y_1982_ = v___x_1985_;
goto v___jp_1981_;
}
v___jp_1981_:
{
lean_object* v___x_1983_; 
lean_inc_ref(v_out_1957_);
v___x_1983_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(v_out_1957_, v_outLv_1958_, v_useAnsi_1959_, v_ws_1948_, v_out_1957_, v_val_1980_, v___y_1982_);
goto v___jp_1966_;
}
}
else
{
lean_dec(v_outputsFile_x3f_1965_);
lean_dec_ref(v_out_1957_);
lean_dec_ref(v_ws_1948_);
goto v___jp_1966_;
}
v___jp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_mk_io_user_error(v___y_1954_);
v___x_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
v___jp_1966_:
{
if (lean_obj_tag(v_out_1961_) == 0)
{
if (v_noBuild_1963_ == 0)
{
lean_object* v_a_1967_; 
lean_dec_ref(v_toMonitorResult_1960_);
v_a_1967_ = lean_ctor_get(v_out_1961_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v_out_1961_);
v___y_1954_ = v_a_1967_;
goto v___jp_1953_;
}
else
{
uint8_t v_wantsRebuild_1968_; 
v_wantsRebuild_1968_ = lean_ctor_get_uint8(v_toMonitorResult_1960_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_1960_);
if (v_wantsRebuild_1968_ == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v_out_1961_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v_out_1961_);
v___y_1954_ = v_a_1969_;
goto v___jp_1953_;
}
else
{
uint8_t v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_out_1961_);
v___x_1970_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0);
v___x_1971_ = lean_io_exit(v___x_1970_);
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_toMonitorResult_1960_);
v_a_1972_ = lean_ctor_get(v_out_1961_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_out_1961_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v_out_1961_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v_out_1961_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 0);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___boxed(lean_object* v_ws_1986_, lean_object* v_cfg_1987_, lean_object* v_ctx_1988_, lean_object* v_result_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(v_ws_1986_, v_cfg_1987_, v_ctx_1988_, v_result_1989_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(lean_object* v_00_u03b1_1992_, lean_object* v_ws_1993_, lean_object* v_cfg_1994_, lean_object* v_ctx_1995_, lean_object* v_result_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(v_ws_1993_, v_cfg_1994_, v_ctx_1995_, v_result_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_ws_2000_, lean_object* v_cfg_2001_, lean_object* v_ctx_2002_, lean_object* v_result_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(v_00_u03b1_1999_, v_ws_2000_, v_cfg_2001_, v_ctx_2002_, v_result_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2006_, lean_object* v_build_2007_, lean_object* v_cfg_2008_, lean_object* v_caption_2009_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2011_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2012_ = lean_st_mk_ref(v___x_2011_);
lean_inc(v___x_2012_);
v___x_2013_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2008_, v___x_2012_);
lean_inc_ref(v_cfg_2008_);
lean_inc_ref(v_ws_2006_);
v___x_2014_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_ws_2006_, v_cfg_2008_, v___x_2012_, v_build_2007_, v_caption_2009_);
lean_inc_ref(v___x_2013_);
v___x_2015_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2013_, v___x_2014_);
v___x_2016_ = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(v_ws_2006_, v_cfg_2008_, v___x_2013_, v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2017_, lean_object* v_build_2018_, lean_object* v_cfg_2019_, lean_object* v_caption_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2017_, v_build_2018_, v_cfg_2019_, v_caption_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2023_, lean_object* v_ws_2024_, lean_object* v_build_2025_, lean_object* v_cfg_2026_, lean_object* v_caption_2027_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2024_, v_build_2025_, v_cfg_2026_, v_caption_2027_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_ws_2031_, lean_object* v_build_2032_, lean_object* v_cfg_2033_, lean_object* v_caption_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2030_, v_ws_2031_, v_build_2032_, v_cfg_2033_, v_caption_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2040_, lean_object* v_job_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v_out_2044_; 
v___x_2043_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2040_, v_job_2041_);
v_out_2044_ = lean_ctor_get(v___x_2043_, 1);
lean_inc_ref(v_out_2044_);
if (lean_obj_tag(v_out_2044_) == 0)
{
lean_object* v_toMonitorResult_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2060_; 
v_toMonitorResult_2045_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v___x_2043_, 1);
lean_dec(v_unused_2061_);
v___x_2047_ = v___x_2043_;
v_isShared_2048_ = v_isSharedCheck_2060_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_toMonitorResult_2045_);
lean_dec(v___x_2043_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2060_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2059_; 
v_a_2049_ = lean_ctor_get(v_out_2044_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_out_2044_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2051_ = v_out_2044_;
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v_out_2044_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v___x_2054_);
v___x_2056_ = v___x_2047_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_toMonitorResult_2045_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2085_; 
v_a_2062_ = lean_ctor_get(v_out_2044_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_out_2044_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2064_ = v_out_2044_;
v_isShared_2065_ = v_isSharedCheck_2085_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v_out_2044_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2085_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_toMonitorResult_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2083_; 
v_toMonitorResult_2066_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2043_, 1);
lean_dec(v_unused_2084_);
v___x_2068_ = v___x_2043_;
v_isShared_2069_ = v_isSharedCheck_2083_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_toMonitorResult_2066_);
lean_dec(v___x_2043_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2083_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_task_2070_; lean_object* v___x_2071_; 
v_task_2070_ = lean_ctor_get(v_a_2062_, 0);
lean_inc_ref(v_task_2070_);
lean_dec(v_a_2062_);
v___x_2071_ = lean_io_wait(v_task_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v_a_2072_);
v___x_2074_ = v___x_2064_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2074_);
v___x_2076_ = v___x_2068_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_toMonitorResult_2066_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_dec_ref(v___x_2071_);
lean_del_object(v___x_2064_);
v___x_2079_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2079_);
v___x_2081_ = v___x_2068_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_toMonitorResult_2066_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2086_, lean_object* v_job_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2086_, v_job_2087_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2090_, lean_object* v_mctx_2091_, lean_object* v_job_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2091_, v_job_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2095_, lean_object* v_mctx_2096_, lean_object* v_job_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2095_, v_mctx_2096_, v_job_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2112_, lean_object* v_build_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v_out_2124_; 
v___x_2115_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2116_ = lean_st_mk_ref(v___x_2115_);
v___x_2117_ = 0;
v___x_2118_ = 1;
v___x_2119_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2116_);
v___x_2120_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2119_, v___x_2116_);
v___x_2121_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2122_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_ws_2112_, v___x_2119_, v___x_2116_, v_build_2113_, v___x_2121_);
v___x_2123_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2120_, v___x_2122_);
v_out_2124_ = lean_ctor_get(v___x_2123_, 1);
lean_inc_ref(v_out_2124_);
lean_dec_ref(v___x_2123_);
if (lean_obj_tag(v_out_2124_) == 0)
{
lean_dec_ref(v_out_2124_);
return v___x_2117_;
}
else
{
lean_dec_ref(v_out_2124_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2125_, lean_object* v_build_2126_, lean_object* v_a_2127_){
_start:
{
uint8_t v_res_2128_; lean_object* v_r_2129_; 
v_res_2128_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2125_, v_build_2126_);
v_r_2129_ = lean_box(v_res_2128_);
return v_r_2129_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2130_, lean_object* v_ws_2131_, lean_object* v_build_2132_){
_start:
{
uint8_t v___x_2134_; 
v___x_2134_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2131_, v_build_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_ws_2136_, lean_object* v_build_2137_, lean_object* v_a_2138_){
_start:
{
uint8_t v_res_2139_; lean_object* v_r_2140_; 
v_res_2139_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2135_, v_ws_2136_, v_build_2137_);
v_r_2140_ = lean_box(v_res_2139_);
return v_r_2140_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2141_, lean_object* v_build_2142_, lean_object* v_cfg_2143_){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2145_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2146_ = lean_st_mk_ref(v___x_2145_);
lean_inc(v___x_2146_);
v___x_2147_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2143_, v___x_2146_);
v___x_2148_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
lean_inc_ref(v_cfg_2143_);
lean_inc_ref(v_ws_2141_);
v___x_2149_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_ws_2141_, v_cfg_2143_, v___x_2146_, v_build_2142_, v___x_2148_);
lean_inc_ref(v___x_2147_);
v___x_2150_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2147_, v___x_2149_);
v___x_2151_ = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(v_ws_2141_, v_cfg_2143_, v___x_2147_, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2152_, lean_object* v_build_2153_, lean_object* v_cfg_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lake_Workspace_runBuild___redArg(v_ws_2152_, v_build_2153_, v_cfg_2154_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2157_, lean_object* v_ws_2158_, lean_object* v_build_2159_, lean_object* v_cfg_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lake_Workspace_runBuild___redArg(v_ws_2158_, v_build_2159_, v_cfg_2160_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_ws_2164_, lean_object* v_build_2165_, lean_object* v_cfg_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lake_Workspace_runBuild(v_00_u03b1_2163_, v_ws_2164_, v_build_2165_, v_cfg_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2169_, lean_object* v_cfg_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lake_Workspace_runBuild___redArg(v_a_2171_, v_build_2169_, v_cfg_2170_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2174_, lean_object* v_cfg_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lake_runBuild___redArg(v_build_2174_, v_cfg_2175_, v_a_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2179_, lean_object* v_build_2180_, lean_object* v_cfg_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lake_Workspace_runBuild___redArg(v_a_2182_, v_build_2180_, v_cfg_2181_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2185_, lean_object* v_build_2186_, lean_object* v_cfg_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lake_runBuild(v_00_u03b1_2185_, v_build_2186_, v_cfg_2187_, v_a_2188_);
return v_res_2190_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Index(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Run(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames);
l_Lake_noBuildCode = _init_l_Lake_noBuildCode();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Run(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Index(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
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
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Run(builtin);
}
#ifdef __cplusplus
}
#endif
