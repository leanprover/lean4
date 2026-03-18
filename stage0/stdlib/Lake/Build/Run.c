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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_io_exit(uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_mono_ms_now();
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* l_Lake_Env_leanGithash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_wait(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_lakeEnv_21_; lean_object* v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
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
v___x_30_ = lean_box(0);
v___x_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_31_, 0, v_config_17_);
lean_ctor_set(v___x_31_, 1, v_ws_16_);
lean_ctor_set(v___x_31_, 2, v___x_29_);
lean_ctor_set(v___x_31_, 3, v___x_20_);
lean_ctor_set(v___x_31_, 4, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object* v_ws_32_, lean_object* v_config_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lake_mkBuildContext(v_ws_32_, v_config_33_);
return v_res_35_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_36_; lean_object* v___x_37_; 
v___x_36_ = 10493;
v___x_37_ = lean_box_uint32(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_38_; lean_object* v___x_39_; 
v___x_38_ = 10491;
v___x_39_ = lean_box_uint32(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_40_; lean_object* v___x_41_; 
v___x_40_ = 10431;
v___x_41_ = lean_box_uint32(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_42_; lean_object* v___x_43_; 
v___x_42_ = 10367;
v___x_43_ = lean_box_uint32(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_44_; lean_object* v___x_45_; 
v___x_44_ = 10463;
v___x_45_ = lean_box_uint32(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_46_; lean_object* v___x_47_; 
v___x_46_ = 10479;
v___x_47_ = lean_box_uint32(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_48_; lean_object* v___x_49_; 
v___x_48_ = 10487;
v___x_49_ = lean_box_uint32(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8(void){
_start:
{
uint32_t v___x_50_; lean_object* v___x_51_; 
v___x_50_ = 10494;
v___x_51_ = lean_box_uint32(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_52_ = lean_unsigned_to_nat(8u);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_54_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8;
v___x_55_ = lean_array_push(v___x_53_, v___x_54_);
v___x_56_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7;
v___x_57_ = lean_array_push(v___x_55_, v___x_56_);
v___x_58_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6;
v___x_59_ = lean_array_push(v___x_57_, v___x_58_);
v___x_60_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5;
v___x_61_ = lean_array_push(v___x_59_, v___x_60_);
v___x_62_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4;
v___x_63_ = lean_array_push(v___x_61_, v___x_62_);
v___x_64_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3;
v___x_65_ = lean_array_push(v___x_63_, v___x_64_);
v___x_66_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2;
v___x_67_ = lean_array_push(v___x_65_, v___x_66_);
v___x_68_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1;
v___x_69_ = lean_array_push(v___x_67_, v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object* v_out_71_, uint8_t v_outLv_72_, uint8_t v_useAnsi_73_, lean_object* v_e_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lake_logToStream(v_e_74_, v_out_71_, v_outLv_72_, v_useAnsi_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object* v_out_77_, lean_object* v_outLv_78_, lean_object* v_useAnsi_79_, lean_object* v_e_80_, lean_object* v___y_81_){
_start:
{
uint8_t v_outLv_boxed_82_; uint8_t v_useAnsi_boxed_83_; lean_object* v_res_84_; 
v_outLv_boxed_82_ = lean_unbox(v_outLv_78_);
v_useAnsi_boxed_83_ = lean_unbox(v_useAnsi_79_);
v_res_84_ = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(v_out_77_, v_outLv_boxed_82_, v_useAnsi_boxed_83_, v_e_80_);
lean_dec_ref(v_e_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object* v_ctx_85_){
_start:
{
lean_object* v_out_86_; uint8_t v_outLv_87_; uint8_t v_useAnsi_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___f_91_; 
v_out_86_ = lean_ctor_get(v_ctx_85_, 1);
lean_inc_ref(v_out_86_);
v_outLv_87_ = lean_ctor_get_uint8(v_ctx_85_, sizeof(void*)*3);
v_useAnsi_88_ = lean_ctor_get_uint8(v_ctx_85_, sizeof(void*)*3 + 4);
lean_dec_ref(v_ctx_85_);
v___x_89_ = lean_box(v_outLv_87_);
v___x_90_ = lean_box(v_useAnsi_88_);
v___f_91_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed), 5, 3);
lean_closure_set(v___f_91_, 0, v_out_86_);
lean_closure_set(v___f_91_, 1, v___x_89_);
lean_closure_set(v___f_91_, 2, v___x_90_);
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* v_ctx_92_, lean_object* v_s_93_, lean_object* v_self_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_apply_3(v_self_94_, v_ctx_92_, v_s_93_, lean_box(0));
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object* v_ctx_97_, lean_object* v_s_98_, lean_object* v_self_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(v_ctx_97_, v_s_98_, v_self_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* v_00_u03b1_102_, lean_object* v_ctx_103_, lean_object* v_s_104_, lean_object* v_self_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_3(v_self_105_, v_ctx_103_, v_s_104_, lean_box(0));
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object* v_00_u03b1_108_, lean_object* v_ctx_109_, lean_object* v_s_110_, lean_object* v_self_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run(v_00_u03b1_108_, v_ctx_109_, v_s_110_, v_self_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* v_out_116_){
_start:
{
lean_object* v_flush_118_; lean_object* v___x_119_; 
v_flush_118_ = lean_ctor_get(v_out_116_, 0);
lean_inc_ref(v_flush_118_);
lean_dec_ref(v_out_116_);
v___x_119_ = lean_apply_1(v_flush_118_, lean_box(0));
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref(v___x_119_);
return v_a_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec_ref(v___x_119_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object* v_out_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lake_Build_Run_0__Lake_flush(v_out_122_);
return v_res_124_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_instMonadST(lean_box(0));
return v___x_125_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_128_ = l_instInhabitedOfMonad___redArg(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17(void){
_start:
{
uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = 1;
v___x_159_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_160_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__17, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
v___x_162_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_163_ = lean_string_append(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_166_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__18, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18);
v___x_167_ = lean_string_append(v___x_166_, v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* v_out_169_, lean_object* v_s_170_){
_start:
{
lean_object* v_putStr_172_; lean_object* v___x_173_; 
v_putStr_172_ = lean_ctor_get(v_out_169_, 4);
lean_inc_ref(v_putStr_172_);
lean_dec_ref(v_out_169_);
lean_inc_ref(v_s_170_);
v___x_173_ = lean_apply_2(v_putStr_172_, v_s_170_, lean_box(0));
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; 
lean_dec_ref(v_s_170_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref(v___x_173_);
return v_a_174_;
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_200_; 
v_a_175_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_200_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_200_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_200_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_179_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_180_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_181_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_182_ = lean_unsigned_to_nat(89u);
v___x_183_ = lean_unsigned_to_nat(4u);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_186_ = lean_io_error_to_string(v_a_175_);
v___x_187_ = lean_string_append(v___x_185_, v___x_186_);
lean_dec_ref(v___x_186_);
v___x_188_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_189_ = lean_string_append(v___x_187_, v___x_188_);
v___x_190_ = l_String_quote(v_s_170_);
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 3);
lean_ctor_set(v___x_177_, 0, v___x_190_);
v___x_192_ = v___x_177_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_199_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_181__overap_197_; lean_object* v___x_198_; 
v___x_193_ = l_Std_Format_defWidth;
v___x_194_ = l_Std_Format_pretty(v___x_192_, v___x_193_, v___x_184_, v___x_184_);
v___x_195_ = lean_string_append(v___x_189_, v___x_194_);
lean_dec_ref(v___x_194_);
v___x_196_ = l_mkPanicMessageWithDecl(v___x_180_, v___x_181_, v___x_182_, v___x_183_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_181__overap_197_ = l_panic___redArg(v___x_179_, v___x_196_);
v___x_198_ = lean_apply_1(v___x_181__overap_197_, lean_box(0));
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object* v_out_201_, lean_object* v_s_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lake_Build_Run_0__Lake_print_x21(v_out_201_, v_s_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* v_s_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_val_210_; lean_object* v_out_212_; lean_object* v_putStr_213_; lean_object* v___x_214_; 
v_out_212_ = lean_ctor_get(v_a_206_, 1);
lean_inc_ref(v_out_212_);
lean_dec_ref(v_a_206_);
v_putStr_213_ = lean_ctor_get(v_out_212_, 4);
lean_inc_ref(v_putStr_213_);
lean_dec_ref(v_out_212_);
lean_inc_ref(v_s_205_);
v___x_214_ = lean_apply_2(v_putStr_213_, v_s_205_, lean_box(0));
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; 
lean_dec_ref(v_s_205_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref(v___x_214_);
v_val_210_ = v_a_215_;
goto v___jp_209_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_241_; 
v_a_216_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_241_ == 0)
{
v___x_218_ = v___x_214_;
v_isShared_219_ = v_isSharedCheck_241_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_241_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_220_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_221_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_222_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_223_ = lean_unsigned_to_nat(89u);
v___x_224_ = lean_unsigned_to_nat(4u);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_227_ = lean_io_error_to_string(v_a_216_);
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
lean_dec_ref(v___x_227_);
v___x_229_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
v___x_231_ = l_String_quote(v_s_205_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 3);
lean_ctor_set(v___x_218_, 0, v___x_231_);
v___x_233_ = v___x_218_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_240_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_808__overap_238_; lean_object* v___x_239_; 
v___x_234_ = l_Std_Format_defWidth;
v___x_235_ = l_Std_Format_pretty(v___x_233_, v___x_234_, v___x_225_, v___x_225_);
v___x_236_ = lean_string_append(v___x_230_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = l_mkPanicMessageWithDecl(v___x_221_, v___x_222_, v___x_223_, v___x_224_, v___x_236_);
lean_dec_ref(v___x_236_);
v___x_808__overap_238_ = l_panic___redArg(v___x_220_, v___x_237_);
v___x_239_ = lean_apply_1(v___x_808__overap_238_, lean_box(0));
v_val_210_ = v___x_239_;
goto v___jp_209_;
}
}
}
v___jp_209_:
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_val_210_);
lean_ctor_set(v___x_211_, 1, v_a_207_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object* v_s_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lake_Build_Run_0__Lake_Monitor_print(v_s_242_, v_a_243_, v_a_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_val_251_; lean_object* v_out_253_; lean_object* v_flush_254_; lean_object* v___x_255_; 
v_out_253_ = lean_ctor_get(v_a_247_, 1);
lean_inc_ref(v_out_253_);
lean_dec_ref(v_a_247_);
v_flush_254_ = lean_ctor_get(v_out_253_, 0);
lean_inc_ref(v_flush_254_);
lean_dec_ref(v_out_253_);
v___x_255_ = lean_apply_1(v_flush_254_, lean_box(0));
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_255_);
v_val_251_ = v_a_256_;
goto v___jp_250_;
}
else
{
lean_object* v___x_257_; 
lean_dec_ref(v___x_255_);
v___x_257_ = lean_box(0);
v_val_251_ = v___x_257_;
goto v___jp_250_;
}
v___jp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_val_251_);
lean_ctor_set(v___x_252_, 1, v_a_248_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lake_Build_Run_0__Lake_Monitor_flush(v_a_258_, v_a_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* v_msg_262_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_9187__overap_265_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
v___x_9187__overap_265_ = lean_panic_fn(v___x_264_, v_msg_262_);
v___x_266_ = lean_apply_1(v___x_9187__overap_265_, lean_box(0));
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object* v_msg_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v_msg_267_);
return v_res_269_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_271_ = lean_array_get_size(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* v_running_278_, lean_object* v_unfinished_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
uint8_t v_showProgress_286_; 
v_showProgress_286_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*3 + 5);
if (v_showProgress_286_ == 0)
{
lean_dec_ref(v_a_280_);
goto v___jp_283_;
}
else
{
uint8_t v_useAnsi_287_; 
v_useAnsi_287_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*3 + 4);
if (v_useAnsi_287_ == 0)
{
lean_dec_ref(v_a_280_);
goto v___jp_283_;
}
else
{
lean_object* v_jobNo_288_; lean_object* v_totalJobs_289_; uint8_t v_wantsRebuild_290_; lean_object* v_failures_291_; lean_object* v_resetCtrl_292_; lean_object* v_lastUpdate_293_; lean_object* v_spinnerIdx_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_383_; 
v_jobNo_288_ = lean_ctor_get(v_a_281_, 0);
v_totalJobs_289_ = lean_ctor_get(v_a_281_, 1);
v_wantsRebuild_290_ = lean_ctor_get_uint8(v_a_281_, sizeof(void*)*6);
v_failures_291_ = lean_ctor_get(v_a_281_, 2);
v_resetCtrl_292_ = lean_ctor_get(v_a_281_, 3);
v_lastUpdate_293_ = lean_ctor_get(v_a_281_, 4);
v_spinnerIdx_294_ = lean_ctor_get(v_a_281_, 5);
v_isSharedCheck_383_ = !lean_is_exclusive(v_a_281_);
if (v_isSharedCheck_383_ == 0)
{
v___x_296_ = v_a_281_;
v_isShared_297_ = v_isSharedCheck_383_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_spinnerIdx_294_);
lean_inc(v_lastUpdate_293_);
lean_inc(v_resetCtrl_292_);
lean_inc(v_failures_291_);
lean_inc(v_totalJobs_289_);
lean_inc(v_jobNo_288_);
lean_dec(v_a_281_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_383_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_out_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v_out_298_ = lean_ctor_get(v_a_280_, 1);
lean_inc_ref(v_out_298_);
lean_dec_ref(v_a_280_);
v___x_299_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_300_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
v___x_301_ = lean_array_fget(v___x_299_, v_spinnerIdx_294_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = l_Fin_add(v___x_300_, v_spinnerIdx_294_, v___x_302_);
lean_dec(v_spinnerIdx_294_);
v___x_304_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(v_totalJobs_289_);
lean_inc(v_jobNo_288_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 5, v___x_303_);
lean_ctor_set(v___x_296_, 3, v___x_304_);
v___x_306_ = v___x_296_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_jobNo_288_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_totalJobs_289_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_failures_291_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_lastUpdate_293_);
lean_ctor_set(v_reuseFailAlloc_382_, 5, v___x_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*6, v_wantsRebuild_290_);
v___x_306_ = v_reuseFailAlloc_382_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v_val_308_; lean_object* v___y_316_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_array_get_size(v_running_278_);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_caption_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = lean_array_get_size(v_unfinished_279_);
v___x_366_ = lean_nat_sub(v___x_365_, v___x_302_);
v___x_367_ = lean_array_fget_borrowed(v_unfinished_279_, v___x_366_);
lean_dec(v___x_366_);
v_caption_368_ = lean_ctor_get(v___x_367_, 2);
v___x_369_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_370_ = lean_string_append(v___x_369_, v_caption_368_);
v___y_316_ = v___x_370_;
goto v___jp_315_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_caption_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_371_ = lean_nat_sub(v___x_363_, v___x_302_);
v___x_372_ = lean_array_fget_borrowed(v_running_278_, v___x_371_);
v_caption_373_ = lean_ctor_get(v___x_372_, 2);
v___x_374_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_375_ = lean_string_append(v___x_374_, v_caption_373_);
v___x_376_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
v___x_377_ = lean_string_append(v___x_375_, v___x_376_);
v___x_378_ = l_Nat_reprFast(v___x_371_);
v___x_379_ = lean_string_append(v___x_377_, v___x_378_);
lean_dec_ref(v___x_378_);
v___x_380_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
v___x_381_ = lean_string_append(v___x_379_, v___x_380_);
v___y_316_ = v___x_381_;
goto v___jp_315_;
}
v___jp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_val_308_);
lean_ctor_set(v___x_309_, 1, v___x_306_);
return v___x_309_;
}
v___jp_310_:
{
lean_object* v_flush_311_; lean_object* v___x_312_; 
v_flush_311_ = lean_ctor_get(v_out_298_, 0);
lean_inc_ref(v_flush_311_);
lean_dec_ref(v_out_298_);
v___x_312_ = lean_apply_1(v_flush_311_, lean_box(0));
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_val_308_ = v_a_313_;
goto v___jp_307_;
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v___x_312_);
v___x_314_ = lean_box(0);
v_val_308_ = v___x_314_;
goto v___jp_307_;
}
}
v___jp_315_:
{
lean_object* v_putStr_317_; lean_object* v___x_318_; uint32_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_putStr_317_ = lean_ctor_get(v_out_298_, 4);
v___x_318_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_319_ = lean_unbox_uint32(v___x_301_);
lean_dec(v___x_301_);
v___x_320_ = lean_string_push(v___x_318_, v___x_319_);
v___x_321_ = lean_string_append(v_resetCtrl_292_, v___x_320_);
lean_dec_ref(v___x_320_);
v___x_322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_323_ = lean_string_append(v___x_321_, v___x_322_);
v___x_324_ = l_Nat_reprFast(v_jobNo_288_);
v___x_325_ = lean_string_append(v___x_323_, v___x_324_);
lean_dec_ref(v___x_324_);
v___x_326_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_327_ = lean_string_append(v___x_325_, v___x_326_);
v___x_328_ = l_Nat_reprFast(v_totalJobs_289_);
v___x_329_ = lean_string_append(v___x_327_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
v___x_332_ = lean_string_append(v___x_331_, v___y_316_);
lean_dec_ref(v___y_316_);
lean_inc_ref(v_putStr_317_);
lean_inc_ref(v___x_332_);
v___x_333_ = lean_apply_2(v_putStr_317_, v___x_332_, lean_box(0));
if (lean_obj_tag(v___x_333_) == 0)
{
lean_dec_ref(v___x_333_);
lean_dec_ref(v___x_332_);
goto v___jp_310_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_361_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_361_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_361_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_361_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_339_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_340_ = lean_unsigned_to_nat(89u);
v___x_341_ = lean_unsigned_to_nat(4u);
v___x_342_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_345_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_344_, v_useAnsi_287_);
v___x_346_ = lean_string_append(v___x_342_, v___x_345_);
lean_dec_ref(v___x_345_);
v___x_347_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_348_ = lean_string_append(v___x_346_, v___x_347_);
v___x_349_ = lean_io_error_to_string(v_a_334_);
v___x_350_ = lean_string_append(v___x_348_, v___x_349_);
lean_dec_ref(v___x_349_);
v___x_351_ = lean_string_append(v___x_350_, v___x_330_);
v___x_352_ = l_String_quote(v___x_332_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 3);
lean_ctor_set(v___x_336_, 0, v___x_352_);
v___x_354_ = v___x_336_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_360_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = l_Std_Format_defWidth;
v___x_356_ = l_Std_Format_pretty(v___x_354_, v___x_355_, v___x_343_, v___x_343_);
v___x_357_ = lean_string_append(v___x_351_, v___x_356_);
lean_dec_ref(v___x_356_);
v___x_358_ = l_mkPanicMessageWithDecl(v___x_338_, v___x_339_, v___x_340_, v___x_341_, v___x_357_);
lean_dec_ref(v___x_357_);
v___x_359_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_358_);
goto v___jp_310_;
}
}
}
}
}
}
}
}
v___jp_283_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v_a_281_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* v_running_384_, lean_object* v_unfinished_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_384_, v_unfinished_385_, v_a_386_, v_a_387_);
lean_dec_ref(v_unfinished_385_);
lean_dec_ref(v_running_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* v_running_390_, lean_object* v_unfinished_391_, lean_object* v_h_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_390_, v_unfinished_391_, v_a_393_, v_a_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* v_running_397_, lean_object* v_unfinished_398_, lean_object* v_h_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(v_running_397_, v_unfinished_398_, v_h_399_, v_a_400_, v_a_401_);
lean_dec_ref(v_unfinished_398_);
lean_dec_ref(v_running_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object* v_ms_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(10000u);
v___x_409_ = lean_nat_dec_lt(v___x_408_, v_ms_407_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(1000u);
v___x_411_ = lean_nat_dec_lt(v___x_410_, v_ms_407_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = l_Nat_reprFast(v_ms_407_);
v___x_413_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0));
v___x_414_ = lean_string_append(v___x_412_, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_415_ = lean_nat_div(v_ms_407_, v___x_410_);
v___x_416_ = l_Nat_reprFast(v___x_415_);
v___x_417_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1));
v___x_418_ = lean_string_append(v___x_416_, v___x_417_);
v___x_419_ = lean_unsigned_to_nat(50u);
v___x_420_ = lean_nat_add(v_ms_407_, v___x_419_);
lean_dec(v_ms_407_);
v___x_421_ = lean_unsigned_to_nat(100u);
v___x_422_ = lean_nat_div(v___x_420_, v___x_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_unsigned_to_nat(10u);
v___x_424_ = lean_nat_mod(v___x_422_, v___x_423_);
lean_dec(v___x_422_);
v___x_425_ = l_Nat_reprFast(v___x_424_);
v___x_426_ = lean_string_append(v___x_418_, v___x_425_);
lean_dec_ref(v___x_425_);
v___x_427_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_428_ = lean_string_append(v___x_426_, v___x_427_);
return v___x_428_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_429_ = lean_unsigned_to_nat(1000u);
v___x_430_ = lean_nat_div(v_ms_407_, v___x_429_);
lean_dec(v_ms_407_);
v___x_431_ = l_Nat_reprFast(v___x_430_);
v___x_432_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_433_ = lean_string_append(v___x_431_, v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* v_out_434_, uint8_t v___y_435_, uint8_t v_useAnsi_436_, lean_object* v_as_437_, size_t v_i_438_, size_t v_stop_439_, lean_object* v_b_440_, lean_object* v___y_441_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_eq(v_i_438_, v_stop_439_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; size_t v___x_446_; size_t v___x_447_; 
v___x_444_ = lean_array_uget_borrowed(v_as_437_, v_i_438_);
lean_inc_ref(v_out_434_);
v___x_445_ = l_Lake_logToStream(v___x_444_, v_out_434_, v___y_435_, v_useAnsi_436_);
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_438_, v___x_446_);
v_i_438_ = v___x_447_;
v_b_440_ = v___x_445_;
goto _start;
}
else
{
lean_object* v___x_449_; 
lean_dec_ref(v_out_434_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_b_440_);
lean_ctor_set(v___x_449_, 1, v___y_441_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* v_out_450_, lean_object* v___y_451_, lean_object* v_useAnsi_452_, lean_object* v_as_453_, lean_object* v_i_454_, lean_object* v_stop_455_, lean_object* v_b_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v___y_17578__boxed_459_; uint8_t v_useAnsi_17579__boxed_460_; size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v___y_17578__boxed_459_ = lean_unbox(v___y_451_);
v_useAnsi_17579__boxed_460_ = lean_unbox(v_useAnsi_452_);
v_i_boxed_461_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_455_);
lean_dec(v_stop_455_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_450_, v___y_17578__boxed_459_, v_useAnsi_17579__boxed_460_, v_as_453_, v_i_boxed_461_, v_stop_boxed_462_, v_b_456_, v___y_457_);
lean_dec_ref(v_as_453_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___y_476_; lean_object* v___y_480_; lean_object* v_val_481_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v_jobNo_495_; lean_object* v_totalJobs_496_; uint8_t v_wantsRebuild_497_; lean_object* v_failures_498_; lean_object* v_resetCtrl_499_; lean_object* v_lastUpdate_500_; lean_object* v_spinnerIdx_501_; lean_object* v_out_502_; uint8_t v_outLv_503_; uint8_t v_failLv_504_; uint8_t v_minAction_505_; uint8_t v_showOptional_506_; uint8_t v_useAnsi_507_; uint8_t v_showProgress_508_; uint8_t v_showTime_509_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; uint8_t v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; uint8_t v___y_533_; uint8_t v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; lean_object* v___y_544_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; uint8_t v___y_608_; lean_object* v___y_609_; lean_object* v_task_611_; lean_object* v_caption_612_; uint8_t v_optional_613_; lean_object* v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; uint32_t v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; uint8_t v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; lean_object* v___y_654_; uint32_t v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; uint8_t v___y_661_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; uint8_t v___y_668_; lean_object* v___y_669_; uint32_t v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; uint32_t v___y_695_; lean_object* v___y_699_; uint8_t v___y_700_; uint8_t v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; uint8_t v___y_709_; lean_object* v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; uint8_t v___y_724_; uint8_t v___y_725_; lean_object* v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; uint8_t v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; uint8_t v___y_734_; uint8_t v___y_735_; uint8_t v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_755_; uint8_t v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; uint8_t v___y_762_; uint8_t v___y_763_; uint8_t v___y_764_; uint8_t v___y_765_; uint8_t v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; uint8_t v___y_785_; lean_object* v___y_786_; uint8_t v___y_787_; uint8_t v___y_788_; uint8_t v___y_789_; lean_object* v___y_794_; uint8_t v___y_795_; uint8_t v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; uint8_t v___y_802_; lean_object* v___y_808_; lean_object* v___y_809_; uint8_t v___y_810_; lean_object* v___y_811_; uint8_t v___y_812_; lean_object* v___y_813_; uint8_t v___y_814_; uint8_t v___y_815_; lean_object* v___y_820_; lean_object* v___x_831_; lean_object* v_a_832_; 
v_jobNo_495_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_jobNo_495_);
v_totalJobs_496_ = lean_ctor_get(v_a_473_, 1);
lean_inc(v_totalJobs_496_);
v_wantsRebuild_497_ = lean_ctor_get_uint8(v_a_473_, sizeof(void*)*6);
v_failures_498_ = lean_ctor_get(v_a_473_, 2);
v_resetCtrl_499_ = lean_ctor_get(v_a_473_, 3);
v_lastUpdate_500_ = lean_ctor_get(v_a_473_, 4);
v_spinnerIdx_501_ = lean_ctor_get(v_a_473_, 5);
v_out_502_ = lean_ctor_get(v_a_472_, 1);
lean_inc_ref(v_out_502_);
v_outLv_503_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3);
v_failLv_504_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3 + 1);
v_minAction_505_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3 + 2);
v_showOptional_506_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3 + 3);
v_useAnsi_507_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3 + 4);
v_showProgress_508_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3 + 5);
v_showTime_509_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3 + 6);
v_task_611_ = lean_ctor_get(v_job_471_, 0);
lean_inc_ref(v_task_611_);
v_caption_612_ = lean_ctor_get(v_job_471_, 2);
lean_inc_ref(v_caption_612_);
v_optional_613_ = lean_ctor_get_uint8(v_job_471_, sizeof(void*)*3);
lean_dec_ref(v_job_471_);
v___x_831_ = lean_task_get_own(v_task_611_);
v_a_832_ = lean_ctor_get(v___x_831_, 1);
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___y_820_ = v_a_832_;
goto v___jp_819_;
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___y_476_);
return v___x_478_;
}
v___jp_479_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_val_481_);
lean_ctor_set(v___x_482_, 1, v___y_480_);
return v___x_482_;
}
v___jp_483_:
{
lean_object* v_out_486_; lean_object* v_flush_487_; lean_object* v___x_488_; 
v_out_486_ = lean_ctor_get(v___y_484_, 1);
lean_inc_ref(v_out_486_);
lean_dec_ref(v___y_484_);
v_flush_487_ = lean_ctor_get(v_out_486_, 0);
lean_inc_ref(v_flush_487_);
lean_dec_ref(v_out_486_);
v___x_488_ = lean_apply_1(v_flush_487_, lean_box(0));
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v___y_480_ = v___y_485_;
v_val_481_ = v_a_489_;
goto v___jp_479_;
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v___x_488_);
v___x_490_ = lean_box(0);
v___y_480_ = v___y_485_;
v_val_481_ = v___x_490_;
goto v___jp_479_;
}
}
v___jp_491_:
{
lean_object* v_snd_494_; 
v_snd_494_ = lean_ctor_get(v___y_493_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___y_493_);
v___y_484_ = v___y_492_;
v___y_485_ = v_snd_494_;
goto v___jp_483_;
}
v___jp_510_:
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v___y_514_, v___y_512_);
lean_dec(v___y_514_);
if (v___x_517_ == 0)
{
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_out_502_);
v___y_484_ = v___y_513_;
v___y_485_ = v___y_515_;
goto v___jp_483_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_nat_dec_le(v___y_512_, v___y_512_);
if (v___x_519_ == 0)
{
if (v___x_517_ == 0)
{
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_out_502_);
v___y_484_ = v___y_513_;
v___y_485_ = v___y_515_;
goto v___jp_483_;
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___y_512_);
lean_dec(v___y_512_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_502_, v___y_516_, v_useAnsi_507_, v___y_511_, v___x_520_, v___x_521_, v___x_518_, v___y_515_);
lean_dec_ref(v___y_511_);
v___y_492_ = v___y_513_;
v___y_493_ = v___x_522_;
goto v___jp_491_;
}
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___y_512_);
lean_dec(v___y_512_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_502_, v___y_516_, v_useAnsi_507_, v___y_511_, v___x_523_, v___x_524_, v___x_518_, v___y_515_);
lean_dec_ref(v___y_511_);
v___y_492_ = v___y_513_;
v___y_493_ = v___x_525_;
goto v___jp_491_;
}
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_dec(v___y_531_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_out_502_);
v___y_484_ = v___y_530_;
v___y_485_ = v___y_532_;
goto v___jp_483_;
}
else
{
if (v___y_533_ == 0)
{
v___y_511_ = v___y_528_;
v___y_512_ = v___y_529_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_531_;
v___y_515_ = v___y_532_;
v___y_516_ = v_outLv_503_;
goto v___jp_510_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
v___y_511_ = v___y_528_;
v___y_512_ = v___y_529_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_531_;
v___y_515_ = v___y_532_;
v___y_516_ = v___x_534_;
goto v___jp_510_;
}
}
}
v___jp_535_:
{
lean_object* v_out_545_; lean_object* v_jobNo_546_; lean_object* v_totalJobs_547_; uint8_t v_wantsRebuild_548_; lean_object* v_failures_549_; lean_object* v_resetCtrl_550_; lean_object* v_lastUpdate_551_; lean_object* v_spinnerIdx_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_598_; 
v_out_545_ = lean_ctor_get(v___y_539_, 1);
v_jobNo_546_ = lean_ctor_get(v___y_542_, 0);
v_totalJobs_547_ = lean_ctor_get(v___y_542_, 1);
v_wantsRebuild_548_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*6);
v_failures_549_ = lean_ctor_get(v___y_542_, 2);
v_resetCtrl_550_ = lean_ctor_get(v___y_542_, 3);
v_lastUpdate_551_ = lean_ctor_get(v___y_542_, 4);
v_spinnerIdx_552_ = lean_ctor_get(v___y_542_, 5);
v_isSharedCheck_598_ = !lean_is_exclusive(v___y_542_);
if (v_isSharedCheck_598_ == 0)
{
v___x_554_ = v___y_542_;
v_isShared_555_ = v_isSharedCheck_598_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_spinnerIdx_552_);
lean_inc(v_lastUpdate_551_);
lean_inc(v_resetCtrl_550_);
lean_inc(v_failures_549_);
lean_inc(v_totalJobs_547_);
lean_inc(v_jobNo_546_);
lean_dec(v___y_542_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_598_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_putStr_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v_putStr_556_ = lean_ctor_get(v_out_545_, 4);
v___x_557_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 3, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_jobNo_546_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_totalJobs_547_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_failures_549_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_lastUpdate_551_);
lean_ctor_set(v_reuseFailAlloc_597_, 5, v_spinnerIdx_552_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*6, v_wantsRebuild_548_);
v___x_559_ = v_reuseFailAlloc_597_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_string_append(v_resetCtrl_550_, v___y_544_);
lean_dec_ref(v___y_544_);
v___x_561_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
lean_inc_ref(v_putStr_556_);
lean_inc_ref(v___x_562_);
v___x_563_ = lean_apply_2(v_putStr_556_, v___x_562_, lean_box(0));
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec_ref(v___x_563_);
lean_dec_ref(v___x_562_);
v___y_527_ = v___y_536_;
v___y_528_ = v___y_537_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_539_;
v___y_531_ = v___y_540_;
v___y_532_ = v___x_559_;
v___y_533_ = v___y_543_;
goto v___jp_526_;
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_596_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_596_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_596_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_596_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_568_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_569_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_570_ = lean_unsigned_to_nat(89u);
v___x_571_ = lean_unsigned_to_nat(4u);
v___x_572_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_573_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7));
v___x_574_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12));
lean_inc(v___y_540_);
v___x_575_ = l_Lean_Name_num___override(v___x_574_, v___y_540_);
v___x_576_ = l_Lean_Name_str___override(v___x_575_, v___x_573_);
v___x_577_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_578_ = l_Lean_Name_str___override(v___x_576_, v___x_577_);
v___x_579_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_578_, v___y_541_);
v___x_580_ = lean_string_append(v___x_572_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_582_ = lean_string_append(v___x_580_, v___x_581_);
v___x_583_ = lean_io_error_to_string(v_a_564_);
v___x_584_ = lean_string_append(v___x_582_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
v___x_587_ = l_String_quote(v___x_562_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 3);
lean_ctor_set(v___x_566_, 0, v___x_587_);
v___x_589_ = v___x_566_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_590_ = l_Std_Format_defWidth;
lean_inc_n(v___y_540_, 2);
v___x_591_ = l_Std_Format_pretty(v___x_589_, v___x_590_, v___y_540_, v___y_540_);
v___x_592_ = lean_string_append(v___x_586_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = l_mkPanicMessageWithDecl(v___x_568_, v___x_569_, v___x_570_, v___x_571_, v___x_592_);
lean_dec_ref(v___x_592_);
v___x_594_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_593_);
v___y_527_ = v___y_536_;
v___y_528_ = v___y_537_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_539_;
v___y_531_ = v___y_540_;
v___y_532_ = v___x_559_;
v___y_533_ = v___y_543_;
goto v___jp_526_;
}
}
}
}
}
}
v___jp_599_:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lake_Ansi_chalk(v___y_609_, v___y_604_);
lean_dec_ref(v___y_604_);
lean_dec_ref(v___y_609_);
v___y_536_ = v___y_600_;
v___y_537_ = v___y_601_;
v___y_538_ = v___y_602_;
v___y_539_ = v___y_603_;
v___y_540_ = v___y_605_;
v___y_541_ = v___y_606_;
v___y_542_ = v___y_607_;
v___y_543_ = v___y_608_;
v___y_544_ = v___x_610_;
goto v___jp_535_;
}
v___jp_614_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_628_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_629_ = lean_string_push(v___x_628_, v___y_620_);
v___x_630_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_631_ = lean_string_append(v___x_629_, v___x_630_);
v___x_632_ = l_Nat_reprFast(v_jobNo_495_);
v___x_633_ = lean_string_append(v___x_631_, v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
v___x_636_ = l_Nat_reprFast(v_totalJobs_496_);
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___x_640_ = lean_string_append(v___x_639_, v___y_623_);
lean_dec_ref(v___y_623_);
v___x_641_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = lean_string_append(v___x_642_, v___y_622_);
lean_dec_ref(v___y_622_);
v___x_644_ = lean_string_append(v___x_643_, v___x_641_);
v___x_645_ = lean_string_append(v___x_644_, v_caption_612_);
lean_dec_ref(v_caption_612_);
v___x_646_ = lean_string_append(v___x_645_, v___y_627_);
lean_dec_ref(v___y_627_);
if (v_useAnsi_507_ == 0)
{
v___y_536_ = v___y_618_;
v___y_537_ = v___y_619_;
v___y_538_ = v___y_615_;
v___y_539_ = v___y_621_;
v___y_540_ = v___y_624_;
v___y_541_ = v___y_625_;
v___y_542_ = v___y_617_;
v___y_543_ = v___y_626_;
v___y_544_ = v___x_646_;
goto v___jp_535_;
}
else
{
if (v___y_618_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_600_ = v___y_618_;
v___y_601_ = v___y_619_;
v___y_602_ = v___y_615_;
v___y_603_ = v___y_621_;
v___y_604_ = v___x_646_;
v___y_605_ = v___y_624_;
v___y_606_ = v___y_625_;
v___y_607_ = v___y_617_;
v___y_608_ = v___y_626_;
v___y_609_ = v___x_647_;
goto v___jp_599_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Lake_LogLevel_ansiColor(v___y_616_);
v___y_600_ = v___y_618_;
v___y_601_ = v___y_619_;
v___y_602_ = v___y_615_;
v___y_603_ = v___y_621_;
v___y_604_ = v___x_646_;
v___y_605_ = v___y_624_;
v___y_606_ = v___y_625_;
v___y_607_ = v___y_617_;
v___y_608_ = v___y_626_;
v___y_609_ = v___x_648_;
goto v___jp_599_;
}
}
}
v___jp_649_:
{
lean_object* v___x_662_; 
v___x_662_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
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
v___y_626_ = v___y_661_;
v___y_627_ = v___x_662_;
goto v___jp_614_;
}
v___jp_663_:
{
if (v_showTime_509_ == 0)
{
lean_dec(v___y_667_);
v___y_650_ = v___y_664_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_668_;
v___y_654_ = v___y_669_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_672_;
v___y_658_ = v___y_676_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
v___y_661_ = v___y_675_;
goto v___jp_649_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_lt(v___y_673_, v___y_667_);
if (v___x_677_ == 0)
{
lean_dec(v___y_667_);
v___y_650_ = v___y_664_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_668_;
v___y_654_ = v___y_669_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_672_;
v___y_658_ = v___y_676_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
v___y_661_ = v___y_675_;
goto v___jp_649_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_678_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_679_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_667_);
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
lean_dec_ref(v___x_679_);
v___x_681_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
v___y_615_ = v___y_664_;
v___y_616_ = v___y_665_;
v___y_617_ = v___y_666_;
v___y_618_ = v___y_668_;
v___y_619_ = v___y_669_;
v___y_620_ = v___y_670_;
v___y_621_ = v___y_671_;
v___y_622_ = v___y_672_;
v___y_623_ = v___y_676_;
v___y_624_ = v___y_673_;
v___y_625_ = v___y_674_;
v___y_626_ = v___y_675_;
v___y_627_ = v___x_682_;
goto v___jp_614_;
}
}
}
v___jp_683_:
{
if (v_optional_613_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_664_ = v___y_687_;
v___y_665_ = v___y_691_;
v___y_666_ = v___y_693_;
v___y_667_ = v___y_684_;
v___y_668_ = v___y_685_;
v___y_669_ = v___y_686_;
v___y_670_ = v___y_695_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_689_;
v___y_673_ = v___y_690_;
v___y_674_ = v___y_692_;
v___y_675_ = v___y_694_;
v___y_676_ = v___x_696_;
goto v___jp_663_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_664_ = v___y_687_;
v___y_665_ = v___y_691_;
v___y_666_ = v___y_693_;
v___y_667_ = v___y_684_;
v___y_668_ = v___y_685_;
v___y_669_ = v___y_686_;
v___y_670_ = v___y_695_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_689_;
v___y_673_ = v___y_690_;
v___y_674_ = v___y_692_;
v___y_675_ = v___y_694_;
v___y_676_ = v___x_697_;
goto v___jp_663_;
}
}
v___jp_698_:
{
if (v___y_700_ == 0)
{
if (v_showProgress_508_ == 0)
{
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_699_);
lean_dec_ref(v_caption_612_);
lean_dec_ref(v_out_502_);
lean_dec(v_totalJobs_496_);
lean_dec(v_jobNo_495_);
v___y_476_ = v___y_708_;
goto v___jp_475_;
}
else
{
if (v_useAnsi_507_ == 0)
{
if (v___y_707_ == 0)
{
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_699_);
lean_dec_ref(v_caption_612_);
lean_dec_ref(v_out_502_);
lean_dec(v_totalJobs_496_);
lean_dec(v_jobNo_495_);
v___y_476_ = v___y_708_;
goto v___jp_475_;
}
else
{
lean_object* v___x_710_; uint32_t v___x_711_; 
v___x_710_ = l_Lake_JobAction_verb(v___y_709_, v___y_701_);
v___x_711_ = 10004;
v___y_684_ = v___y_699_;
v___y_685_ = v___y_700_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_703_;
v___y_688_ = v___y_704_;
v___y_689_ = v___x_710_;
v___y_690_ = v___y_705_;
v___y_691_ = v___y_706_;
v___y_692_ = v___y_707_;
v___y_693_ = v___y_708_;
v___y_694_ = v___y_709_;
v___y_695_ = v___x_711_;
goto v___jp_683_;
}
}
else
{
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_699_);
lean_dec_ref(v_caption_612_);
lean_dec_ref(v_out_502_);
lean_dec(v_totalJobs_496_);
lean_dec(v_jobNo_495_);
v___y_476_ = v___y_708_;
goto v___jp_475_;
}
}
}
else
{
lean_object* v___x_712_; uint32_t v___x_713_; 
v___x_712_ = l_Lake_JobAction_verb(v___y_709_, v___y_701_);
v___x_713_ = l_Lake_LogLevel_icon(v___y_706_);
v___y_684_ = v___y_699_;
v___y_685_ = v___y_700_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_703_;
v___y_688_ = v___y_704_;
v___y_689_ = v___x_712_;
v___y_690_ = v___y_705_;
v___y_691_ = v___y_706_;
v___y_692_ = v___y_700_;
v___y_693_ = v___y_708_;
v___y_694_ = v___y_709_;
v___y_695_ = v___x_713_;
goto v___jp_683_;
}
}
v___jp_714_:
{
if (v_optional_613_ == 0)
{
v___y_699_ = v___y_715_;
v___y_700_ = v___y_725_;
v___y_701_ = v___y_716_;
v___y_702_ = v___y_717_;
v___y_703_ = v___y_718_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_721_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_723_;
v___y_709_ = v___y_724_;
goto v___jp_698_;
}
else
{
if (v_showOptional_506_ == 0)
{
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_715_);
lean_dec_ref(v_caption_612_);
lean_dec_ref(v_out_502_);
lean_dec(v_totalJobs_496_);
lean_dec(v_jobNo_495_);
v___y_476_ = v___y_723_;
goto v___jp_475_;
}
else
{
v___y_699_ = v___y_715_;
v___y_700_ = v___y_725_;
v___y_701_ = v___y_716_;
v___y_702_ = v___y_717_;
v___y_703_ = v___y_718_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_721_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_723_;
v___y_709_ = v___y_724_;
goto v___jp_698_;
}
}
}
v___jp_726_:
{
if (v___y_736_ == 0)
{
if (v___y_728_ == 0)
{
v___y_715_ = v___y_727_;
v___y_716_ = v___y_730_;
v___y_717_ = v___y_729_;
v___y_718_ = v___y_731_;
v___y_719_ = v___y_737_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_738_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_728_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___y_727_;
v___y_716_ = v___y_730_;
v___y_717_ = v___y_729_;
v___y_718_ = v___y_731_;
v___y_719_ = v___y_737_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_738_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_735_;
goto v___jp_714_;
}
}
else
{
if (v_optional_613_ == 0)
{
lean_object* v_jobNo_739_; lean_object* v_totalJobs_740_; uint8_t v_wantsRebuild_741_; lean_object* v_failures_742_; lean_object* v_resetCtrl_743_; lean_object* v_lastUpdate_744_; lean_object* v_spinnerIdx_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_jobNo_739_ = lean_ctor_get(v___y_738_, 0);
v_totalJobs_740_ = lean_ctor_get(v___y_738_, 1);
v_wantsRebuild_741_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*6);
v_failures_742_ = lean_ctor_get(v___y_738_, 2);
v_resetCtrl_743_ = lean_ctor_get(v___y_738_, 3);
v_lastUpdate_744_ = lean_ctor_get(v___y_738_, 4);
v_spinnerIdx_745_ = lean_ctor_get(v___y_738_, 5);
v_isSharedCheck_753_ = !lean_is_exclusive(v___y_738_);
if (v_isSharedCheck_753_ == 0)
{
v___x_747_ = v___y_738_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_spinnerIdx_745_);
lean_inc(v_lastUpdate_744_);
lean_inc(v_resetCtrl_743_);
lean_inc(v_failures_742_);
lean_inc(v_totalJobs_740_);
lean_inc(v_jobNo_739_);
lean_dec(v___y_738_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
lean_inc_ref(v_caption_612_);
v___x_749_ = lean_array_push(v_failures_742_, v_caption_612_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 2, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_jobNo_739_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_totalJobs_740_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_resetCtrl_743_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_lastUpdate_744_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v_spinnerIdx_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*6, v_wantsRebuild_741_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
v___y_715_ = v___y_727_;
v___y_716_ = v___y_730_;
v___y_717_ = v___y_729_;
v___y_718_ = v___y_731_;
v___y_719_ = v___y_737_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___x_751_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_736_;
goto v___jp_714_;
}
}
}
else
{
v___y_715_ = v___y_727_;
v___y_716_ = v___y_730_;
v___y_717_ = v___y_729_;
v___y_718_ = v___y_731_;
v___y_719_ = v___y_737_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_738_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_736_;
goto v___jp_714_;
}
}
}
v___jp_754_:
{
if (v___y_760_ == 0)
{
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_759_;
v___y_732_ = v___y_761_;
v___y_733_ = v___y_762_;
v___y_734_ = v___y_765_;
v___y_735_ = v___y_763_;
v___y_736_ = v___y_764_;
v___y_737_ = v_a_472_;
v___y_738_ = v_a_473_;
goto v___jp_726_;
}
else
{
if (v_wantsRebuild_497_ == 0)
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_inc(v_spinnerIdx_501_);
lean_inc(v_lastUpdate_500_);
lean_inc_ref(v_resetCtrl_499_);
lean_inc_ref(v_failures_498_);
v_isSharedCheck_772_ = !lean_is_exclusive(v_a_473_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_773_ = lean_ctor_get(v_a_473_, 5);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_a_473_, 4);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_a_473_, 3);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_a_473_, 2);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_a_473_, 1);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_a_473_, 0);
lean_dec(v_unused_778_);
v___x_767_ = v_a_473_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_dec(v_a_473_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
lean_inc(v_totalJobs_496_);
lean_inc(v_jobNo_495_);
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_jobNo_495_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_totalJobs_496_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_failures_498_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_resetCtrl_499_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_lastUpdate_500_);
lean_ctor_set(v_reuseFailAlloc_771_, 5, v_spinnerIdx_501_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*6, v___y_760_);
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_759_;
v___y_732_ = v___y_761_;
v___y_733_ = v___y_762_;
v___y_734_ = v___y_765_;
v___y_735_ = v___y_763_;
v___y_736_ = v___y_764_;
v___y_737_ = v_a_472_;
v___y_738_ = v___x_770_;
goto v___jp_726_;
}
}
}
else
{
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_759_;
v___y_732_ = v___y_761_;
v___y_733_ = v___y_762_;
v___y_734_ = v___y_765_;
v___y_735_ = v___y_763_;
v___y_736_ = v___y_764_;
v___y_737_ = v_a_472_;
v___y_738_ = v_a_473_;
goto v___jp_726_;
}
}
}
v___jp_779_:
{
uint8_t v___x_790_; 
v___x_790_ = l_Lake_instOrdJobAction_ord(v_minAction_505_, v___y_783_);
if (v___x_790_ == 2)
{
uint8_t v___x_791_; 
v___x_791_ = 0;
v___y_755_ = v___y_781_;
v___y_756_ = v___y_780_;
v___y_757_ = v___y_783_;
v___y_758_ = v___y_782_;
v___y_759_ = v___y_784_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_786_;
v___y_762_ = v___y_787_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_788_;
v___y_765_ = v___x_791_;
goto v___jp_754_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = 1;
v___y_755_ = v___y_781_;
v___y_756_ = v___y_780_;
v___y_757_ = v___y_783_;
v___y_758_ = v___y_782_;
v___y_759_ = v___y_784_;
v___y_760_ = v___y_785_;
v___y_761_ = v___y_786_;
v___y_762_ = v___y_787_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_788_;
v___y_765_ = v___x_792_;
goto v___jp_754_;
}
}
v___jp_793_:
{
uint8_t v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_strict_and(v___y_795_, v___y_802_);
v___x_804_ = l_Lake_instOrdLogLevel_ord(v_outLv_503_, v___y_801_);
if (v___x_804_ == 2)
{
uint8_t v___x_805_; 
v___x_805_ = 0;
v___y_780_ = v___y_795_;
v___y_781_ = v___y_794_;
v___y_782_ = v___y_797_;
v___y_783_ = v___y_796_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_799_;
v___y_786_ = v___y_800_;
v___y_787_ = v___y_801_;
v___y_788_ = v___x_803_;
v___y_789_ = v___x_805_;
goto v___jp_779_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = 1;
v___y_780_ = v___y_795_;
v___y_781_ = v___y_794_;
v___y_782_ = v___y_797_;
v___y_783_ = v___y_796_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_799_;
v___y_786_ = v___y_800_;
v___y_787_ = v___y_801_;
v___y_788_ = v___x_803_;
v___y_789_ = v___x_806_;
goto v___jp_779_;
}
}
v___jp_807_:
{
uint8_t v___x_816_; 
v___x_816_ = l_Lake_instOrdLogLevel_ord(v_failLv_504_, v___y_814_);
if (v___x_816_ == 2)
{
uint8_t v___x_817_; 
v___x_817_ = 0;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_815_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_809_;
v___y_798_ = v___y_811_;
v___y_799_ = v___y_812_;
v___y_800_ = v___y_813_;
v___y_801_ = v___y_814_;
v___y_802_ = v___x_817_;
goto v___jp_793_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = 1;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_815_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_809_;
v___y_798_ = v___y_811_;
v___y_799_ = v___y_812_;
v___y_800_ = v___y_813_;
v___y_801_ = v___y_814_;
v___y_802_ = v___x_818_;
goto v___jp_793_;
}
}
v___jp_819_:
{
lean_object* v_log_821_; uint8_t v_action_822_; uint8_t v_wantsRebuild_823_; lean_object* v_buildTime_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_log_821_ = lean_ctor_get(v___y_820_, 0);
lean_inc_ref(v_log_821_);
v_action_822_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*3);
v_wantsRebuild_823_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*3 + 1);
v_buildTime_824_ = lean_ctor_get(v___y_820_, 2);
lean_inc(v_buildTime_824_);
lean_dec_ref(v___y_820_);
v___x_825_ = l_Lake_Log_maxLv(v_log_821_);
v___x_826_ = lean_array_get_size(v_log_821_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_nat_dec_eq(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = 1;
v___y_808_ = v_buildTime_824_;
v___y_809_ = v_log_821_;
v___y_810_ = v_action_822_;
v___y_811_ = v___x_826_;
v___y_812_ = v_wantsRebuild_823_;
v___y_813_ = v___x_827_;
v___y_814_ = v___x_825_;
v___y_815_ = v___x_829_;
goto v___jp_807_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = 0;
v___y_808_ = v_buildTime_824_;
v___y_809_ = v_log_821_;
v___y_810_ = v_action_822_;
v___y_811_ = v___x_826_;
v___y_812_ = v_wantsRebuild_823_;
v___y_813_ = v___x_827_;
v___y_814_ = v___x_825_;
v___y_815_ = v___x_830_;
goto v___jp_807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_833_, v_a_834_, v_a_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_838_, uint8_t v___y_839_, uint8_t v_useAnsi_840_, lean_object* v_as_841_, size_t v_i_842_, size_t v_stop_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_838_, v___y_839_, v_useAnsi_840_, v_as_841_, v_i_842_, v_stop_843_, v_b_844_, v___y_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_849_, lean_object* v___y_850_, lean_object* v_useAnsi_851_, lean_object* v_as_852_, lean_object* v_i_853_, lean_object* v_stop_854_, lean_object* v_b_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___y_18355__boxed_859_; uint8_t v_useAnsi_18356__boxed_860_; size_t v_i_boxed_861_; size_t v_stop_boxed_862_; lean_object* v_res_863_; 
v___y_18355__boxed_859_ = lean_unbox(v___y_850_);
v_useAnsi_18356__boxed_860_ = lean_unbox(v_useAnsi_851_);
v_i_boxed_861_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_stop_boxed_862_ = lean_unbox_usize(v_stop_854_);
lean_dec(v_stop_854_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_849_, v___y_18355__boxed_859_, v_useAnsi_18356__boxed_860_, v_as_852_, v_i_boxed_861_, v_stop_boxed_862_, v_b_855_, v___y_856_, v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v_as_852_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object* v_as_864_, size_t v_i_865_, size_t v_stop_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_fst_872_; lean_object* v_snd_873_; uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_eq(v_i_865_, v_stop_866_);
if (v___x_877_ == 0)
{
lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_880_; lean_object* v_task_881_; uint8_t v___x_882_; 
v_fst_878_ = lean_ctor_get(v_b_867_, 0);
v_snd_879_ = lean_ctor_get(v_b_867_, 1);
v___x_880_ = lean_array_uget_borrowed(v_as_864_, v_i_865_);
v_task_881_ = lean_ctor_get(v___x_880_, 0);
v___x_882_ = lean_io_get_task_state(v_task_881_);
switch(v___x_882_)
{
case 0:
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_890_; 
lean_inc(v_snd_879_);
lean_inc(v_fst_878_);
v_isSharedCheck_890_ = !lean_is_exclusive(v_b_867_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_891_ = lean_ctor_get(v_b_867_, 1);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_b_867_, 0);
lean_dec(v_unused_892_);
v___x_884_ = v_b_867_;
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_b_867_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_inc(v___x_880_);
v___x_886_ = lean_array_push(v_snd_879_, v___x_880_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_fst_872_ = v___x_888_;
v_snd_873_ = v___y_869_;
goto v___jp_871_;
}
}
}
case 1:
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_901_; 
lean_inc(v_snd_879_);
lean_inc(v_fst_878_);
v_isSharedCheck_901_ = !lean_is_exclusive(v_b_867_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_902_ = lean_ctor_get(v_b_867_, 1);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_b_867_, 0);
lean_dec(v_unused_903_);
v___x_894_ = v_b_867_;
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
else
{
lean_dec(v_b_867_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_inc(v___x_880_);
v___x_896_ = lean_array_push(v_fst_878_, v___x_880_);
lean_inc(v___x_880_);
v___x_897_ = lean_array_push(v_snd_879_, v___x_880_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_897_);
lean_ctor_set(v___x_894_, 0, v___x_896_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
v_fst_872_ = v___x_899_;
v_snd_873_ = v___y_869_;
goto v___jp_871_;
}
}
}
default: 
{
lean_object* v___x_904_; lean_object* v_snd_905_; lean_object* v_jobNo_906_; lean_object* v_totalJobs_907_; uint8_t v_wantsRebuild_908_; lean_object* v_failures_909_; lean_object* v_resetCtrl_910_; lean_object* v_lastUpdate_911_; lean_object* v_spinnerIdx_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
lean_inc_ref(v___y_868_);
lean_inc(v___x_880_);
v___x_904_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_880_, v___y_868_, v___y_869_);
v_snd_905_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_snd_905_);
lean_dec_ref(v___x_904_);
v_jobNo_906_ = lean_ctor_get(v_snd_905_, 0);
v_totalJobs_907_ = lean_ctor_get(v_snd_905_, 1);
v_wantsRebuild_908_ = lean_ctor_get_uint8(v_snd_905_, sizeof(void*)*6);
v_failures_909_ = lean_ctor_get(v_snd_905_, 2);
v_resetCtrl_910_ = lean_ctor_get(v_snd_905_, 3);
v_lastUpdate_911_ = lean_ctor_get(v_snd_905_, 4);
v_spinnerIdx_912_ = lean_ctor_get(v_snd_905_, 5);
v_isSharedCheck_921_ = !lean_is_exclusive(v_snd_905_);
if (v_isSharedCheck_921_ == 0)
{
v___x_914_ = v_snd_905_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_spinnerIdx_912_);
lean_inc(v_lastUpdate_911_);
lean_inc(v_resetCtrl_910_);
lean_inc(v_failures_909_);
lean_inc(v_totalJobs_907_);
lean_inc(v_jobNo_906_);
lean_dec(v_snd_905_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_jobNo_906_, v___x_916_);
lean_dec(v_jobNo_906_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_totalJobs_907_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_failures_909_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_resetCtrl_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_lastUpdate_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_spinnerIdx_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*6, v_wantsRebuild_908_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
v_fst_872_ = v_b_867_;
v_snd_873_ = v___x_919_;
goto v___jp_871_;
}
}
}
}
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v___y_868_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_b_867_);
lean_ctor_set(v___x_922_, 1, v___y_869_);
return v___x_922_;
}
v___jp_871_:
{
size_t v___x_874_; size_t v___x_875_; 
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_865_, v___x_874_);
v_i_865_ = v___x_875_;
v_b_867_ = v_fst_872_;
v___y_869_ = v_snd_873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object* v_as_923_, lean_object* v_i_924_, lean_object* v_stop_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
size_t v_i_boxed_930_; size_t v_stop_boxed_931_; lean_object* v_res_932_; 
v_i_boxed_930_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_stop_boxed_931_ = lean_unbox_usize(v_stop_925_);
lean_dec(v_stop_925_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v_as_923_, v_i_boxed_930_, v_stop_boxed_931_, v_b_926_, v___y_927_, v___y_928_);
lean_dec_ref(v_as_923_);
return v_res_932_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object* v_unfinished_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_jobs_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_jobNo_944_; lean_object* v_totalJobs_945_; uint8_t v_wantsRebuild_946_; lean_object* v_failures_947_; lean_object* v_resetCtrl_948_; lean_object* v_lastUpdate_949_; lean_object* v_spinnerIdx_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_987_; 
v_jobs_939_ = lean_ctor_get(v_a_936_, 0);
v___x_940_ = lean_st_ref_take(v_jobs_939_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_943_ = lean_st_ref_set(v_jobs_939_, v___x_942_);
v_jobNo_944_ = lean_ctor_get(v_a_937_, 0);
v_totalJobs_945_ = lean_ctor_get(v_a_937_, 1);
v_wantsRebuild_946_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*6);
v_failures_947_ = lean_ctor_get(v_a_937_, 2);
v_resetCtrl_948_ = lean_ctor_get(v_a_937_, 3);
v_lastUpdate_949_ = lean_ctor_get(v_a_937_, 4);
v_spinnerIdx_950_ = lean_ctor_get(v_a_937_, 5);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_937_);
if (v_isSharedCheck_987_ == 0)
{
v___x_952_ = v_a_937_;
v_isShared_953_ = v_isSharedCheck_987_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_spinnerIdx_950_);
lean_inc(v_lastUpdate_949_);
lean_inc(v_resetCtrl_948_);
lean_inc(v_failures_947_);
lean_inc(v_totalJobs_945_);
lean_inc(v_jobNo_944_);
lean_dec(v_a_937_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_987_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___y_956_; lean_object* v_fst_957_; lean_object* v_snd_958_; lean_object* v___y_968_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_954_ = lean_array_get_size(v___x_940_);
v___x_971_ = lean_nat_add(v_totalJobs_945_, v___x_954_);
lean_dec(v_totalJobs_945_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_971_);
v___x_973_ = v___x_952_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_jobNo_944_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_failures_947_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_resetCtrl_948_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_lastUpdate_949_);
lean_ctor_set(v_reuseFailAlloc_986_, 5, v_spinnerIdx_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_986_, sizeof(void*)*6, v_wantsRebuild_946_);
v___x_973_ = v_reuseFailAlloc_986_;
goto v_reusejp_972_;
}
v___jp_955_:
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_lt(v___x_941_, v___x_954_);
if (v___x_959_ == 0)
{
lean_dec_ref(v_snd_958_);
lean_dec_ref(v_fst_957_);
lean_dec(v___x_940_);
lean_dec_ref(v_a_936_);
return v___y_956_;
}
else
{
uint8_t v___x_960_; 
v___x_960_ = lean_nat_dec_le(v___x_954_, v___x_954_);
if (v___x_960_ == 0)
{
if (v___x_959_ == 0)
{
lean_dec_ref(v_snd_958_);
lean_dec_ref(v_fst_957_);
lean_dec(v___x_940_);
lean_dec_ref(v_a_936_);
return v___y_956_;
}
else
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
lean_dec_ref(v___y_956_);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = lean_usize_of_nat(v___x_954_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v___x_940_, v___x_961_, v___x_962_, v_fst_957_, v_a_936_, v_snd_958_);
lean_dec(v___x_940_);
return v___x_963_;
}
}
else
{
size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v___y_956_);
v___x_964_ = ((size_t)0ULL);
v___x_965_ = lean_usize_of_nat(v___x_954_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v___x_940_, v___x_964_, v___x_965_, v_fst_957_, v_a_936_, v_snd_958_);
lean_dec(v___x_940_);
return v___x_966_;
}
}
}
v___jp_967_:
{
lean_object* v_fst_969_; lean_object* v_snd_970_; 
v_fst_969_ = lean_ctor_get(v___y_968_, 0);
lean_inc(v_fst_969_);
v_snd_970_ = lean_ctor_get(v___y_968_, 1);
lean_inc(v_snd_970_);
v___y_956_ = v___y_968_;
v_fst_957_ = v_fst_969_;
v_snd_958_ = v_snd_970_;
goto v___jp_955_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0);
v___x_975_ = lean_array_get_size(v_unfinished_935_);
v___x_976_ = lean_nat_dec_lt(v___x_941_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_inc_ref(v___x_973_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_974_);
lean_ctor_set(v___x_977_, 1, v___x_973_);
v___y_956_ = v___x_977_;
v_fst_957_ = v___x_974_;
v_snd_958_ = v___x_973_;
goto v___jp_955_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = lean_nat_dec_le(v___x_975_, v___x_975_);
if (v___x_978_ == 0)
{
if (v___x_976_ == 0)
{
lean_object* v___x_979_; 
lean_inc_ref(v___x_973_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_974_);
lean_ctor_set(v___x_979_, 1, v___x_973_);
v___y_956_ = v___x_979_;
v_fst_957_ = v___x_974_;
v_snd_958_ = v___x_973_;
goto v___jp_955_;
}
else
{
size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((size_t)0ULL);
v___x_981_ = lean_usize_of_nat(v___x_975_);
lean_inc_ref(v_a_936_);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v_unfinished_935_, v___x_980_, v___x_981_, v___x_974_, v_a_936_, v___x_973_);
v___y_968_ = v___x_982_;
goto v___jp_967_;
}
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_975_);
lean_inc_ref(v_a_936_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(v_unfinished_935_, v___x_983_, v___x_984_, v___x_974_, v_a_936_, v___x_973_);
v___y_968_ = v___x_985_;
goto v___jp_967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object* v_unfinished_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lake_Build_Run_0__Lake_Monitor_poll(v_unfinished_988_, v_a_989_, v_a_990_);
lean_dec_ref(v_unfinished_988_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___y_997_; lean_object* v___x_1015_; lean_object* v_lastUpdate_1016_; lean_object* v_updateFrequency_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1015_ = lean_io_mono_ms_now();
v_lastUpdate_1016_ = lean_ctor_get(v_a_994_, 4);
v_updateFrequency_1017_ = lean_ctor_get(v_a_993_, 2);
v___x_1018_ = lean_nat_sub(v___x_1015_, v_lastUpdate_1016_);
lean_dec(v___x_1015_);
v___x_1019_ = lean_nat_sub(v_updateFrequency_1017_, v___x_1018_);
lean_dec(v___x_1018_);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_nat_dec_lt(v___x_1020_, v___x_1019_);
if (v___x_1021_ == 0)
{
lean_dec(v___x_1019_);
v___y_997_ = v_a_994_;
goto v___jp_996_;
}
else
{
uint32_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_uint32_of_nat(v___x_1019_);
lean_dec(v___x_1019_);
v___x_1023_ = l_IO_sleep(v___x_1022_);
v___y_997_ = v_a_994_;
goto v___jp_996_;
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v_jobNo_999_; lean_object* v_totalJobs_1000_; uint8_t v_wantsRebuild_1001_; lean_object* v_failures_1002_; lean_object* v_resetCtrl_1003_; lean_object* v_spinnerIdx_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1013_; 
v___x_998_ = lean_io_mono_ms_now();
v_jobNo_999_ = lean_ctor_get(v___y_997_, 0);
v_totalJobs_1000_ = lean_ctor_get(v___y_997_, 1);
v_wantsRebuild_1001_ = lean_ctor_get_uint8(v___y_997_, sizeof(void*)*6);
v_failures_1002_ = lean_ctor_get(v___y_997_, 2);
v_resetCtrl_1003_ = lean_ctor_get(v___y_997_, 3);
v_spinnerIdx_1004_ = lean_ctor_get(v___y_997_, 5);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___y_997_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v___y_997_, 4);
lean_dec(v_unused_1014_);
v___x_1006_ = v___y_997_;
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_spinnerIdx_1004_);
lean_inc(v_resetCtrl_1003_);
lean_inc(v_failures_1002_);
lean_inc(v_totalJobs_1000_);
lean_inc(v_jobNo_999_);
lean_dec(v___y_997_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 4, v___x_998_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_jobNo_999_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_totalJobs_1000_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_failures_1002_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_resetCtrl_1003_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_spinnerIdx_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*6, v_wantsRebuild_1001_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1008_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1024_, v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_unfinished_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v_fst_1033_; lean_object* v_snd_1034_; lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1052_; 
lean_inc_ref(v_a_1029_);
v___x_1032_ = l___private_Lake_Build_Run_0__Lake_Monitor_poll(v_unfinished_1028_, v_a_1029_, v_a_1030_);
lean_dec_ref(v_unfinished_1028_);
v_fst_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_fst_1033_);
v_snd_1034_ = lean_ctor_get(v___x_1032_, 1);
lean_inc(v_snd_1034_);
lean_dec_ref(v___x_1032_);
v_fst_1035_ = lean_ctor_get(v_fst_1033_, 0);
v_snd_1036_ = lean_ctor_get(v_fst_1033_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_fst_1033_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1038_ = v_fst_1033_;
v_isShared_1039_ = v_isSharedCheck_1052_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v_fst_1033_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1052_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_array_get_size(v_snd_1036_);
v___x_1042_ = lean_nat_dec_lt(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec(v_snd_1036_);
lean_dec(v_fst_1035_);
lean_dec_ref(v_a_1029_);
v___x_1043_ = lean_box(0);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v_snd_1034_);
lean_ctor_set(v___x_1038_, 0, v___x_1043_);
v___x_1045_ = v___x_1038_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1034_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v_snd_1048_; lean_object* v___x_1049_; lean_object* v_snd_1050_; 
lean_del_object(v___x_1038_);
lean_inc_ref(v_a_1029_);
v___x_1047_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1035_, v_snd_1036_, v_a_1029_, v_snd_1034_);
lean_dec(v_fst_1035_);
v_snd_1048_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_snd_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1029_, v_snd_1048_);
v_snd_1050_ = lean_ctor_get(v___x_1049_, 1);
lean_inc(v_snd_1050_);
lean_dec_ref(v___x_1049_);
v_unfinished_1028_ = v_snd_1036_;
v_a_1030_ = v_snd_1050_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_unfinished_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_unfinished_1053_, v_a_1054_, v_a_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v_snd_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1123_; 
lean_inc_ref(v_a_1059_);
v___x_1062_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_init_1058_, v_a_1059_, v_a_1060_);
v_snd_1063_ = lean_ctor_get(v___x_1062_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___x_1062_, 0);
lean_dec(v_unused_1124_);
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1123_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_snd_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1123_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_jobNo_1067_; lean_object* v_totalJobs_1068_; uint8_t v_wantsRebuild_1069_; lean_object* v_failures_1070_; lean_object* v_resetCtrl_1071_; lean_object* v_lastUpdate_1072_; lean_object* v_spinnerIdx_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1122_; 
v_jobNo_1067_ = lean_ctor_get(v_snd_1063_, 0);
v_totalJobs_1068_ = lean_ctor_get(v_snd_1063_, 1);
v_wantsRebuild_1069_ = lean_ctor_get_uint8(v_snd_1063_, sizeof(void*)*6);
v_failures_1070_ = lean_ctor_get(v_snd_1063_, 2);
v_resetCtrl_1071_ = lean_ctor_get(v_snd_1063_, 3);
v_lastUpdate_1072_ = lean_ctor_get(v_snd_1063_, 4);
v_spinnerIdx_1073_ = lean_ctor_get(v_snd_1063_, 5);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_snd_1063_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1075_ = v_snd_1063_;
v_isShared_1076_ = v_isSharedCheck_1122_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_spinnerIdx_1073_);
lean_inc(v_lastUpdate_1072_);
lean_inc(v_resetCtrl_1071_);
lean_inc(v_failures_1070_);
lean_inc(v_totalJobs_1068_);
lean_inc(v_jobNo_1067_);
lean_dec(v_snd_1063_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1122_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 3, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_jobNo_1067_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_totalJobs_1068_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_failures_1070_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_lastUpdate_1072_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_spinnerIdx_1073_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6, v_wantsRebuild_1069_);
v___x_1079_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v_val_1081_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_string_utf8_byte_size(v_resetCtrl_1071_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_nat_dec_eq(v___x_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v_out_1088_; lean_object* v_flush_1089_; lean_object* v_putStr_1090_; lean_object* v___x_1095_; 
v_out_1088_ = lean_ctor_get(v_a_1059_, 1);
lean_inc_ref(v_out_1088_);
lean_dec_ref(v_a_1059_);
v_flush_1089_ = lean_ctor_get(v_out_1088_, 0);
lean_inc_ref(v_flush_1089_);
v_putStr_1090_ = lean_ctor_get(v_out_1088_, 4);
lean_inc_ref(v_putStr_1090_);
lean_dec_ref(v_out_1088_);
lean_inc_ref(v_resetCtrl_1071_);
v___x_1095_ = lean_apply_2(v_putStr_1090_, v_resetCtrl_1071_, lean_box(0));
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_resetCtrl_1071_);
goto v___jp_1091_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1118_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1118_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1118_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1100_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1101_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1102_ = lean_unsigned_to_nat(89u);
v___x_1103_ = lean_unsigned_to_nat(4u);
v___x_1104_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1105_ = lean_io_error_to_string(v_a_1096_);
v___x_1106_ = lean_string_append(v___x_1104_, v___x_1105_);
lean_dec_ref(v___x_1105_);
v___x_1107_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
v___x_1109_ = l_String_quote(v_resetCtrl_1071_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 3);
lean_ctor_set(v___x_1098_, 0, v___x_1109_);
v___x_1111_ = v___x_1098_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1112_ = l_Std_Format_defWidth;
v___x_1113_ = l_Std_Format_pretty(v___x_1111_, v___x_1112_, v___x_1086_, v___x_1086_);
v___x_1114_ = lean_string_append(v___x_1108_, v___x_1113_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = l_mkPanicMessageWithDecl(v___x_1100_, v___x_1101_, v___x_1102_, v___x_1103_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1115_);
goto v___jp_1091_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_apply_1(v_flush_1089_, lean_box(0));
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1092_);
v_val_1081_ = v_a_1093_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1094_; 
lean_dec_ref(v___x_1092_);
v___x_1094_ = lean_box(0);
v_val_1081_ = v___x_1094_;
goto v___jp_1080_;
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v_resetCtrl_1071_);
lean_del_object(v___x_1065_);
lean_dec_ref(v_a_1059_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1079_);
return v___x_1120_;
}
v___jp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1079_);
lean_ctor_set(v___x_1065_, 0, v_val_1081_);
v___x_1083_ = v___x_1065_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_val_1081_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1079_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1125_, v_a_1126_, v_a_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1130_){
_start:
{
lean_object* v_failures_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_failures_1131_ = lean_ctor_get(v_self_1130_, 0);
v___x_1132_ = lean_array_get_size(v_failures_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1135_);
lean_dec_ref(v_self_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1138_, lean_object* v_jobs_1139_){
_start:
{
lean_object* v_toLogConfig_1141_; uint8_t v_verbosity_1142_; uint8_t v_failLv_1143_; uint8_t v_outLv_1144_; uint8_t v_ansiMode_1145_; lean_object* v_out_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; uint8_t v___x_1150_; uint8_t v___x_1151_; uint8_t v___y_1153_; uint8_t v___y_1154_; uint8_t v___y_1158_; 
v_toLogConfig_1141_ = lean_ctor_get(v_cfg_1138_, 0);
v_verbosity_1142_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*2 + 3);
v_failLv_1143_ = lean_ctor_get_uint8(v_toLogConfig_1141_, sizeof(void*)*1);
v_outLv_1144_ = lean_ctor_get_uint8(v_toLogConfig_1141_, sizeof(void*)*1 + 1);
v_ansiMode_1145_ = lean_ctor_get_uint8(v_toLogConfig_1141_, sizeof(void*)*1 + 2);
v_out_1146_ = lean_ctor_get(v_toLogConfig_1141_, 0);
v___x_1147_ = l_Lake_OutStream_get(v_out_1146_);
lean_inc_ref(v___x_1147_);
v___x_1148_ = l_Lake_AnsiMode_isEnabled(v___x_1147_, v_ansiMode_1145_);
v___x_1149_ = l_Lake_BuildConfig_showProgress(v_cfg_1138_);
v___x_1150_ = 2;
v___x_1151_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1142_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1160_; 
v___x_1160_ = 2;
v___y_1158_ = v___x_1160_;
goto v___jp_1157_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = 0;
v___y_1158_ = v___x_1161_;
goto v___jp_1157_;
}
v___jp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(100u);
v___x_1156_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v___x_1156_, 0, v_jobs_1139_);
lean_ctor_set(v___x_1156_, 1, v___x_1147_);
lean_ctor_set(v___x_1156_, 2, v___x_1155_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3, v_outLv_1144_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 1, v_failLv_1143_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 2, v___y_1153_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 3, v___x_1151_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 4, v___x_1148_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 5, v___x_1149_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 6, v___y_1154_);
return v___x_1156_;
}
v___jp_1157_:
{
if (v___x_1151_ == 0)
{
if (v___x_1148_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = 1;
v___y_1153_ = v___y_1158_;
v___y_1154_ = v___x_1159_;
goto v___jp_1152_;
}
else
{
v___y_1153_ = v___y_1158_;
v___y_1154_ = v___x_1151_;
goto v___jp_1152_;
}
}
else
{
v___y_1153_ = v___y_1158_;
v___y_1154_ = v___x_1151_;
goto v___jp_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1162_, lean_object* v_jobs_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1162_, v_jobs_1163_);
lean_dec_ref(v_cfg_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1166_, lean_object* v_initJobs_1167_, lean_object* v_initFailures_1168_, lean_object* v_resetCtrl_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_snd_1176_; lean_object* v_totalJobs_1177_; uint8_t v_wantsRebuild_1178_; lean_object* v_failures_1179_; lean_object* v___x_1180_; 
v___x_1171_ = lean_io_mono_ms_now();
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = 0;
v___x_1174_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1172_);
lean_ctor_set(v___x_1174_, 2, v_initFailures_1168_);
lean_ctor_set(v___x_1174_, 3, v_resetCtrl_1169_);
lean_ctor_set(v___x_1174_, 4, v___x_1171_);
lean_ctor_set(v___x_1174_, 5, v___x_1172_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*6, v___x_1173_);
v___x_1175_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1167_, v_ctx_1166_, v___x_1174_);
v_snd_1176_ = lean_ctor_get(v___x_1175_, 1);
lean_inc(v_snd_1176_);
lean_dec_ref(v___x_1175_);
v_totalJobs_1177_ = lean_ctor_get(v_snd_1176_, 1);
lean_inc(v_totalJobs_1177_);
v_wantsRebuild_1178_ = lean_ctor_get_uint8(v_snd_1176_, sizeof(void*)*6);
v_failures_1179_ = lean_ctor_get(v_snd_1176_, 2);
lean_inc_ref(v_failures_1179_);
lean_dec(v_snd_1176_);
v___x_1180_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1180_, 0, v_failures_1179_);
lean_ctor_set(v___x_1180_, 1, v_totalJobs_1177_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*2, v_wantsRebuild_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1181_, lean_object* v_initJobs_1182_, lean_object* v_initFailures_1183_, lean_object* v_resetCtrl_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1181_, v_initJobs_1182_, v_initFailures_1183_, v_resetCtrl_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1187_, lean_object* v_jobs_1188_, lean_object* v_out_1189_, uint8_t v_failLv_1190_, uint8_t v_outLv_1191_, uint8_t v_minAction_1192_, uint8_t v_showOptional_1193_, uint8_t v_useAnsi_1194_, uint8_t v_showProgress_1195_, uint8_t v_showTime_1196_, lean_object* v_resetCtrl_1197_, lean_object* v_initFailures_1198_, lean_object* v_updateFrequency_1199_){
_start:
{
lean_object* v_ctx_1201_; lean_object* v___x_1202_; 
v_ctx_1201_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v_ctx_1201_, 0, v_jobs_1188_);
lean_ctor_set(v_ctx_1201_, 1, v_out_1189_);
lean_ctor_set(v_ctx_1201_, 2, v_updateFrequency_1199_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3, v_outLv_1191_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3 + 1, v_failLv_1190_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3 + 2, v_minAction_1192_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3 + 3, v_showOptional_1193_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3 + 4, v_useAnsi_1194_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3 + 5, v_showProgress_1195_);
lean_ctor_set_uint8(v_ctx_1201_, sizeof(void*)*3 + 6, v_showTime_1196_);
v___x_1202_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1201_, v_initJobs_1187_, v_initFailures_1198_, v_resetCtrl_1197_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1203_, lean_object* v_jobs_1204_, lean_object* v_out_1205_, lean_object* v_failLv_1206_, lean_object* v_outLv_1207_, lean_object* v_minAction_1208_, lean_object* v_showOptional_1209_, lean_object* v_useAnsi_1210_, lean_object* v_showProgress_1211_, lean_object* v_showTime_1212_, lean_object* v_resetCtrl_1213_, lean_object* v_initFailures_1214_, lean_object* v_updateFrequency_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_failLv_boxed_1217_; uint8_t v_outLv_boxed_1218_; uint8_t v_minAction_boxed_1219_; uint8_t v_showOptional_boxed_1220_; uint8_t v_useAnsi_boxed_1221_; uint8_t v_showProgress_boxed_1222_; uint8_t v_showTime_boxed_1223_; lean_object* v_res_1224_; 
v_failLv_boxed_1217_ = lean_unbox(v_failLv_1206_);
v_outLv_boxed_1218_ = lean_unbox(v_outLv_1207_);
v_minAction_boxed_1219_ = lean_unbox(v_minAction_1208_);
v_showOptional_boxed_1220_ = lean_unbox(v_showOptional_1209_);
v_useAnsi_boxed_1221_ = lean_unbox(v_useAnsi_1210_);
v_showProgress_boxed_1222_ = lean_unbox(v_showProgress_1211_);
v_showTime_boxed_1223_ = lean_unbox(v_showTime_1212_);
v_res_1224_ = l_Lake_monitorJobs(v_initJobs_1203_, v_jobs_1204_, v_out_1205_, v_failLv_boxed_1217_, v_outLv_boxed_1218_, v_minAction_boxed_1219_, v_showOptional_boxed_1220_, v_useAnsi_boxed_1221_, v_showProgress_boxed_1222_, v_showTime_boxed_1223_, v_resetCtrl_1213_, v_initFailures_1214_, v_updateFrequency_1215_);
return v_res_1224_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1225_; 
v___x_1225_ = 3;
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1226_, lean_object* v_x_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_apply_2(v_logger_1226_, v___y_1228_, lean_box(0));
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1231_, lean_object* v_x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1231_, v_x_1232_, v___y_1233_);
return v_res_1235_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1240_ = l_String_quote(v___x_1239_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2);
v___x_1242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = l_Std_Format_defWidth;
v___x_1245_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3);
v___x_1246_ = l_Std_Format_pretty(v___x_1245_, v___x_1244_, v___x_1243_, v___x_1243_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1249_ = l_String_quote(v___x_1248_);
return v___x_1249_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = l_Std_Format_defWidth;
v___x_1254_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_1255_ = l_Std_Format_pretty(v___x_1254_, v___x_1253_, v___x_1252_, v___x_1252_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
v___x_1258_ = l_String_quote(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = l_Std_Format_defWidth;
v___x_1263_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_1264_ = l_Std_Format_pretty(v___x_1263_, v___x_1262_, v___x_1261_, v___x_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1266_, lean_object* v_ws_1267_, lean_object* v_outputsRef_x3f_1268_, lean_object* v_out_1269_, lean_object* v_outputsFile_1270_, uint8_t v_isVerbose_1271_){
_start:
{
lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1293_; lean_object* v___y_1294_; uint8_t v___x_1381_; 
lean_inc_ref(v_logger_1266_);
v___f_1275_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1275_, 0, v_logger_1266_);
v___x_1276_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1381_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1267_);
if (v___x_1381_ == 0)
{
lean_object* v_root_1382_; lean_object* v_baseName_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_root_1382_ = lean_ctor_get(v_ws_1267_, 0);
lean_inc_ref(v_root_1382_);
lean_dec_ref(v_ws_1267_);
v_baseName_1383_ = lean_ctor_get(v_root_1382_, 1);
lean_inc(v_baseName_1383_);
lean_dec_ref(v_root_1382_);
v___x_1384_ = l_Lean_Name_toString(v_baseName_1383_, v___x_1381_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
v___x_1387_ = 2;
v___x_1388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*1, v___x_1387_);
v___x_1389_ = lean_apply_2(v_logger_1266_, v___x_1388_, lean_box(0));
goto v___jp_1308_;
}
else
{
lean_dec_ref(v_ws_1267_);
lean_dec_ref(v_logger_1266_);
goto v___jp_1308_;
}
v___jp_1273_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_box(0);
return v___x_1274_;
}
v___jp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = lean_array_get_size(v___y_1278_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_nat_dec_lt(v___y_1279_, v___x_1280_);
if (v___x_1282_ == 0)
{
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___f_1275_);
return v___x_1281_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_nat_dec_le(v___x_1280_, v___x_1280_);
if (v___x_1283_ == 0)
{
if (v___x_1282_ == 0)
{
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___f_1275_);
return v___x_1281_;
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_2378__overap_1286_; lean_object* v___x_1287_; 
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1280_);
v___x_2378__overap_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1276_, v___f_1275_, v___y_1278_, v___x_1284_, v___x_1285_, v___x_1281_);
v___x_1287_ = lean_apply_1(v___x_2378__overap_1286_, lean_box(0));
return v___x_1287_;
}
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_2382__overap_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1280_);
v___x_2382__overap_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1276_, v___f_1275_, v___y_1278_, v___x_1288_, v___x_1289_, v___x_1281_);
v___x_1291_ = lean_apply_1(v___x_2382__overap_1290_, lean_box(0));
return v___x_1291_;
}
}
}
v___jp_1292_:
{
if (v_isVerbose_1271_ == 0)
{
lean_object* v___x_1295_; 
lean_dec_ref(v___y_1294_);
lean_dec_ref(v___f_1275_);
v___x_1295_ = lean_box(0);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = lean_array_get_size(v___y_1294_);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_nat_dec_lt(v___y_1293_, v___x_1296_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___y_1294_);
lean_dec_ref(v___f_1275_);
return v___x_1297_;
}
else
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_nat_dec_le(v___x_1296_, v___x_1296_);
if (v___x_1299_ == 0)
{
if (v___x_1298_ == 0)
{
lean_dec_ref(v___y_1294_);
lean_dec_ref(v___f_1275_);
return v___x_1297_;
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_2285__overap_1302_; lean_object* v___x_1303_; 
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = lean_usize_of_nat(v___x_1296_);
v___x_2285__overap_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1276_, v___f_1275_, v___y_1294_, v___x_1300_, v___x_1301_, v___x_1297_);
v___x_1303_ = lean_apply_1(v___x_2285__overap_1302_, lean_box(0));
return v___x_1303_;
}
}
else
{
size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_2289__overap_1306_; lean_object* v___x_1307_; 
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = lean_usize_of_nat(v___x_1296_);
v___x_2289__overap_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1276_, v___f_1275_, v___y_1294_, v___x_1304_, v___x_1305_, v___x_1297_);
v___x_1307_ = lean_apply_1(v___x_2289__overap_1306_, lean_box(0));
return v___x_1307_;
}
}
}
}
v___jp_1308_:
{
if (lean_obj_tag(v_outputsRef_x3f_1268_) == 1)
{
lean_object* v_val_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_val_1309_ = lean_ctor_get(v_outputsRef_x3f_1268_, 0);
v___x_1310_ = lean_st_ref_get(v_val_1309_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1313_ = l_Lake_CacheMap_writeFile(v_outputsFile_1270_, v___x_1310_, v___x_1312_);
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
if (v_isVerbose_1271_ == 0)
{
lean_dec(v_a_1314_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_out_1269_);
goto v___jp_1273_;
}
else
{
lean_object* v_putStr_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_putStr_1317_ = lean_ctor_get(v_out_1269_, 4);
lean_inc_ref(v_putStr_1317_);
lean_dec_ref(v_out_1269_);
v___x_1318_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1319_ = lean_apply_2(v_putStr_1317_, v___x_1318_, lean_box(0));
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref(v___x_1319_);
v___y_1278_ = v_a_1314_;
v___y_1279_ = v___x_1311_;
goto v___jp_1277_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_2520__overap_1339_; lean_object* v___x_1340_; 
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
v___x_1328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1327_, v_isVerbose_1271_);
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
v___x_2520__overap_1339_ = l_panic___redArg(v___x_1321_, v___x_1338_);
v___x_1340_ = lean_apply_1(v___x_2520__overap_1339_, lean_box(0));
v___y_1278_ = v_a_1314_;
v___y_1279_ = v___x_1311_;
goto v___jp_1277_;
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_out_1269_);
goto v___jp_1273_;
}
}
else
{
lean_object* v_a_1341_; lean_object* v_putStr_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1341_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1313_);
v_putStr_1342_ = lean_ctor_get(v_out_1269_, 4);
lean_inc_ref(v_putStr_1342_);
lean_dec_ref(v_out_1269_);
v___x_1343_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1344_ = lean_apply_2(v_putStr_1342_, v___x_1343_, lean_box(0));
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_dec_ref(v___x_1344_);
v___y_1293_ = v___x_1311_;
v___y_1294_ = v_a_1341_;
goto v___jp_1292_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_2180__overap_1359_; lean_object* v___x_1360_; 
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
v___x_2180__overap_1359_ = l_panic___redArg(v___x_1346_, v___x_1358_);
v___x_1360_ = lean_apply_1(v___x_2180__overap_1359_, lean_box(0));
v___y_1293_ = v___x_1311_;
v___y_1294_ = v_a_1341_;
goto v___jp_1292_;
}
}
}
else
{
lean_object* v_putStr_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___f_1275_);
lean_dec_ref(v_outputsFile_1270_);
v_putStr_1361_ = lean_ctor_get(v_out_1269_, 4);
lean_inc_ref(v_putStr_1361_);
lean_dec_ref(v_out_1269_);
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
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_2335__overap_1379_; lean_object* v___x_1380_; 
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
v___x_2335__overap_1379_ = l_panic___redArg(v___x_1366_, v___x_1378_);
v___x_1380_ = lean_apply_1(v___x_2335__overap_1379_, lean_box(0));
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1390_, lean_object* v_ws_1391_, lean_object* v_outputsRef_x3f_1392_, lean_object* v_out_1393_, lean_object* v_outputsFile_1394_, lean_object* v_isVerbose_1395_, lean_object* v_a_1396_){
_start:
{
uint8_t v_isVerbose_boxed_1397_; lean_object* v_res_1398_; 
v_isVerbose_boxed_1397_ = lean_unbox(v_isVerbose_1395_);
v_res_1398_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1390_, v_ws_1391_, v_outputsRef_x3f_1392_, v_out_1393_, v_outputsFile_1394_, v_isVerbose_boxed_1397_);
lean_dec(v_outputsRef_x3f_1392_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1400_, lean_object* v_as_1401_, size_t v_i_1402_, size_t v_stop_1403_, lean_object* v_b_1404_){
_start:
{
lean_object* v_val_1407_; uint8_t v___x_1411_; 
v___x_1411_ = lean_usize_dec_eq(v_i_1402_, v_stop_1403_);
if (v___x_1411_ == 0)
{
lean_object* v_putStr_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_putStr_1412_ = lean_ctor_get(v_out_1400_, 4);
v___x_1413_ = lean_array_uget_borrowed(v_as_1401_, v_i_1402_);
v___x_1414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1415_ = lean_string_append(v___x_1414_, v___x_1413_);
v___x_1416_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
lean_inc_ref(v_putStr_1412_);
lean_inc_ref(v___x_1417_);
v___x_1418_ = lean_apply_2(v_putStr_1412_, v___x_1417_, lean_box(0));
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; 
lean_dec_ref(v___x_1417_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v_val_1407_ = v_a_1419_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1443_; 
v_a_1420_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1443_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1443_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1424_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1426_ = lean_unsigned_to_nat(89u);
v___x_1427_ = lean_unsigned_to_nat(4u);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1430_ = lean_io_error_to_string(v_a_1420_);
v___x_1431_ = lean_string_append(v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1433_ = lean_string_append(v___x_1431_, v___x_1432_);
v___x_1434_ = l_String_quote(v___x_1417_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 3);
lean_ctor_set(v___x_1422_, 0, v___x_1434_);
v___x_1436_ = v___x_1422_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1437_ = l_Std_Format_defWidth;
v___x_1438_ = l_Std_Format_pretty(v___x_1436_, v___x_1437_, v___x_1428_, v___x_1428_);
v___x_1439_ = lean_string_append(v___x_1433_, v___x_1438_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = l_mkPanicMessageWithDecl(v___x_1424_, v___x_1425_, v___x_1426_, v___x_1427_, v___x_1439_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1440_);
v_val_1407_ = v___x_1441_;
goto v___jp_1406_;
}
}
}
}
else
{
lean_dec_ref(v_out_1400_);
return v_b_1404_;
}
v___jp_1406_:
{
size_t v___x_1408_; size_t v___x_1409_; 
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_add(v_i_1402_, v___x_1408_);
v_i_1402_ = v___x_1409_;
v_b_1404_ = v_val_1407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1444_, lean_object* v_as_1445_, lean_object* v_i_1446_, lean_object* v_stop_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_){
_start:
{
size_t v_i_boxed_1450_; size_t v_stop_boxed_1451_; lean_object* v_res_1452_; 
v_i_boxed_1450_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_stop_boxed_1451_ = lean_unbox_usize(v_stop_1447_);
lean_dec(v_stop_1447_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1444_, v_as_1445_, v_i_boxed_1450_, v_stop_boxed_1451_, v_b_1448_);
lean_dec_ref(v_as_1445_);
return v_res_1452_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1460_ = l_String_quote(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_Std_Format_defWidth;
v___x_1465_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1466_ = l_Std_Format_pretty(v___x_1465_, v___x_1464_, v___x_1463_, v___x_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1467_, lean_object* v_out_1468_, lean_object* v_result_1469_){
_start:
{
uint8_t v___y_1472_; lean_object* v___y_1473_; lean_object* v_failures_1547_; lean_object* v_numJobs_1548_; uint8_t v___y_1550_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_failures_1547_ = lean_ctor_get(v_result_1469_, 0);
lean_inc_ref(v_failures_1547_);
v_numJobs_1548_ = lean_ctor_get(v_result_1469_, 1);
lean_inc(v_numJobs_1548_);
lean_dec_ref(v_result_1469_);
v___x_1558_ = lean_array_get_size(v_failures_1547_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = lean_nat_dec_eq(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v_flush_1561_; lean_object* v_putStr_1562_; lean_object* v___y_1568_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_numJobs_1548_);
v_flush_1561_ = lean_ctor_get(v_out_1468_, 0);
lean_inc_ref(v_flush_1561_);
v_putStr_1562_ = lean_ctor_get(v_out_1468_, 4);
v___x_1579_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
lean_inc_ref(v_putStr_1562_);
v___x_1580_ = lean_apply_2(v_putStr_1562_, v___x_1579_, lean_box(0));
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec_ref(v___x_1580_);
goto v___jp_1569_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1583_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1584_ = lean_unsigned_to_nat(89u);
v___x_1585_ = lean_unsigned_to_nat(4u);
v___x_1586_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1587_ = lean_io_error_to_string(v_a_1581_);
v___x_1588_ = lean_string_append(v___x_1586_, v___x_1587_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1590_ = lean_string_append(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1592_ = lean_string_append(v___x_1590_, v___x_1591_);
v___x_1593_ = l_mkPanicMessageWithDecl(v___x_1582_, v___x_1583_, v___x_1584_, v___x_1585_, v___x_1592_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1593_);
goto v___jp_1569_;
}
v___jp_1563_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_apply_1(v_flush_1561_, lean_box(0));
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
return v_a_1565_;
}
else
{
lean_object* v___x_1566_; 
lean_dec_ref(v___x_1564_);
v___x_1566_ = lean_box(0);
return v___x_1566_;
}
}
v___jp_1567_:
{
goto v___jp_1563_;
}
v___jp_1569_:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_nat_dec_lt(v___x_1559_, v___x_1558_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v_failures_1547_);
lean_dec_ref(v_out_1468_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_nat_dec_le(v___x_1558_, v___x_1558_);
if (v___x_1572_ == 0)
{
if (v___x_1570_ == 0)
{
lean_dec_ref(v_failures_1547_);
lean_dec_ref(v_out_1468_);
goto v___jp_1563_;
}
else
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = lean_usize_of_nat(v___x_1558_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1468_, v_failures_1547_, v___x_1573_, v___x_1574_, v___x_1571_);
lean_dec_ref(v_failures_1547_);
v___y_1568_ = v___x_1575_;
goto v___jp_1567_;
}
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1558_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1468_, v_failures_1547_, v___x_1576_, v___x_1577_, v___x_1571_);
lean_dec_ref(v_failures_1547_);
v___y_1568_ = v___x_1578_;
goto v___jp_1567_;
}
}
}
}
else
{
uint8_t v___x_1595_; 
lean_dec_ref(v_failures_1547_);
v___x_1595_ = l_Lake_BuildConfig_showProgress(v_cfg_1467_);
if (v___x_1595_ == 0)
{
v___y_1550_ = v___x_1595_;
goto v___jp_1549_;
}
else
{
uint8_t v_showSuccess_1596_; 
v_showSuccess_1596_ = lean_ctor_get_uint8(v_cfg_1467_, sizeof(void*)*2 + 4);
v___y_1550_ = v_showSuccess_1596_;
goto v___jp_1549_;
}
}
v___jp_1471_:
{
uint8_t v_noBuild_1474_; 
v_noBuild_1474_ = lean_ctor_get_uint8(v_cfg_1467_, sizeof(void*)*2 + 2);
if (v_noBuild_1474_ == 0)
{
lean_object* v_putStr_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_putStr_1475_ = lean_ctor_get(v_out_1468_, 4);
lean_inc_ref(v_putStr_1475_);
lean_dec_ref(v_out_1468_);
v___x_1476_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1477_ = lean_string_append(v___x_1476_, v___y_1473_);
lean_dec_ref(v___y_1473_);
v___x_1478_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1479_ = lean_string_append(v___x_1477_, v___x_1478_);
lean_inc_ref(v___x_1479_);
v___x_1480_ = lean_apply_2(v_putStr_1475_, v___x_1479_, lean_box(0));
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; 
lean_dec_ref(v___x_1479_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v___x_1480_);
return v_a_1481_;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1510_; 
v_a_1482_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1484_ = v___x_1480_;
v_isShared_1485_ = v_isSharedCheck_1510_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1510_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1486_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1487_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1488_ = lean_unsigned_to_nat(89u);
v___x_1489_ = lean_unsigned_to_nat(4u);
v___x_1490_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1492_, v___y_1472_);
v___x_1494_ = lean_string_append(v___x_1490_, v___x_1493_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1496_ = lean_string_append(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_io_error_to_string(v_a_1482_);
v___x_1498_ = lean_string_append(v___x_1496_, v___x_1497_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1500_ = lean_string_append(v___x_1498_, v___x_1499_);
v___x_1501_ = l_String_quote(v___x_1479_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 3);
lean_ctor_set(v___x_1484_, 0, v___x_1501_);
v___x_1503_ = v___x_1484_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1504_ = l_Std_Format_defWidth;
v___x_1505_ = l_Std_Format_pretty(v___x_1503_, v___x_1504_, v___x_1491_, v___x_1491_);
v___x_1506_ = lean_string_append(v___x_1500_, v___x_1505_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_mkPanicMessageWithDecl(v___x_1486_, v___x_1487_, v___x_1488_, v___x_1489_, v___x_1506_);
lean_dec_ref(v___x_1506_);
v___x_1508_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1507_);
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_putStr_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_putStr_1511_ = lean_ctor_get(v_out_1468_, 4);
lean_inc_ref(v_putStr_1511_);
lean_dec_ref(v_out_1468_);
v___x_1512_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1513_ = lean_string_append(v___x_1512_, v___y_1473_);
lean_dec_ref(v___y_1473_);
v___x_1514_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1515_ = lean_string_append(v___x_1513_, v___x_1514_);
lean_inc_ref(v___x_1515_);
v___x_1516_ = lean_apply_2(v_putStr_1511_, v___x_1515_, lean_box(0));
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; 
lean_dec_ref(v___x_1515_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
return v_a_1517_;
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1546_; 
v_a_1518_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1520_ = v___x_1516_;
v_isShared_1521_ = v_isSharedCheck_1546_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1546_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1522_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1523_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1524_ = lean_unsigned_to_nat(89u);
v___x_1525_ = lean_unsigned_to_nat(4u);
v___x_1526_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1529_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1528_, v_noBuild_1474_);
v___x_1530_ = lean_string_append(v___x_1526_, v___x_1529_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1532_ = lean_string_append(v___x_1530_, v___x_1531_);
v___x_1533_ = lean_io_error_to_string(v_a_1518_);
v___x_1534_ = lean_string_append(v___x_1532_, v___x_1533_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1536_ = lean_string_append(v___x_1534_, v___x_1535_);
v___x_1537_ = l_String_quote(v___x_1515_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 3);
lean_ctor_set(v___x_1520_, 0, v___x_1537_);
v___x_1539_ = v___x_1520_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = l_Std_Format_defWidth;
v___x_1541_ = l_Std_Format_pretty(v___x_1539_, v___x_1540_, v___x_1527_, v___x_1527_);
v___x_1542_ = lean_string_append(v___x_1536_, v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = l_mkPanicMessageWithDecl(v___x_1522_, v___x_1523_, v___x_1524_, v___x_1525_, v___x_1542_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1543_);
return v___x_1544_;
}
}
}
}
}
v___jp_1549_:
{
if (v___y_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_numJobs_1548_);
lean_dec_ref(v_out_1468_);
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_dec_eq(v_numJobs_1548_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = l_Nat_reprFast(v_numJobs_1548_);
v___x_1555_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
v___y_1472_ = v___y_1550_;
v___y_1473_ = v___x_1556_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1557_; 
lean_dec(v_numJobs_1548_);
v___x_1557_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1472_ = v___y_1550_;
v___y_1473_ = v___x_1557_;
goto v___jp_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1597_, lean_object* v_out_1598_, lean_object* v_result_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1597_, v_out_1598_, v_result_1599_);
lean_dec_ref(v_cfg_1597_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1602_){
_start:
{
lean_object* v_toMonitorResult_1603_; 
v_toMonitorResult_1603_ = lean_ctor_get(v_self_1602_, 0);
lean_inc_ref(v_toMonitorResult_1603_);
return v_toMonitorResult_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1604_);
lean_dec_ref(v_self_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1607_){
_start:
{
lean_object* v___f_1608_; 
v___f_1608_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1608_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1609_){
_start:
{
lean_object* v_out_1610_; 
v_out_1610_ = lean_ctor_get(v_self_1609_, 1);
if (lean_obj_tag(v_out_1610_) == 0)
{
uint8_t v___x_1611_; 
v___x_1611_ = 0;
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; 
v___x_1612_ = 1;
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1613_);
lean_dec_ref(v_self_1613_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1616_, lean_object* v_self_1617_){
_start:
{
lean_object* v_out_1618_; 
v_out_1618_ = lean_ctor_get(v_self_1617_, 1);
if (lean_obj_tag(v_out_1618_) == 0)
{
uint8_t v___x_1619_; 
v___x_1619_ = 0;
return v___x_1619_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = 1;
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1621_, lean_object* v_self_1622_){
_start:
{
uint8_t v_res_1623_; lean_object* v_r_1624_; 
v_res_1623_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1621_, v_self_1622_);
lean_dec_ref(v_self_1622_);
v_r_1624_ = lean_box(v_res_1623_);
return v_r_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1633_, lean_object* v_job_1634_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_failures_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
lean_inc_ref(v_job_1634_);
v___x_1636_ = l_Lake_Job_toOpaque___redArg(v_job_1634_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_mk_empty_array_with_capacity(v___x_1637_);
v___x_1639_ = lean_array_push(v___x_1638_, v___x_1636_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1642_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1643_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1633_, v___x_1639_, v___x_1641_, v___x_1642_);
v_failures_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc_ref(v_failures_1644_);
v___x_1645_ = lean_array_get_size(v_failures_1644_);
lean_dec_ref(v_failures_1644_);
v___x_1646_ = lean_nat_dec_eq(v___x_1645_, v___x_1640_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v_job_1634_);
v___x_1647_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1643_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
return v___x_1648_;
}
else
{
lean_object* v_task_1649_; lean_object* v___x_1650_; 
v_task_1649_ = lean_ctor_get(v_job_1634_, 0);
lean_inc_ref(v_task_1649_);
lean_dec_ref(v_job_1634_);
v___x_1650_ = lean_io_wait(v_task_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v___x_1650_, 1);
lean_dec(v_unused_1660_);
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_a_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v___x_1655_);
lean_ctor_set(v___x_1653_, 0, v___x_1643_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; lean_object* v_unused_1670_; 
v_unused_1669_ = lean_ctor_get(v___x_1650_, 1);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v___x_1650_, 0);
lean_dec(v_unused_1670_);
v___x_1662_ = v___x_1650_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v___x_1650_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 0);
lean_ctor_set(v___x_1662_, 1, v___x_1664_);
lean_ctor_set(v___x_1662_, 0, v___x_1643_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1671_, lean_object* v_job_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1671_, v_job_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1675_, lean_object* v_ctx_1676_, lean_object* v_job_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1676_, v_job_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_ctx_1681_, lean_object* v_job_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1680_, v_ctx_1681_, v_job_1682_);
return v_res_1684_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_unsigned_to_nat(16u);
v___x_1689_ = lean_mk_array(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___x_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* v_ws_1693_, lean_object* v_cfg_1694_, lean_object* v_jobs_1695_){
_start:
{
lean_object* v_val_1698_; lean_object* v_outputsFile_x3f_1710_; 
v_outputsFile_x3f_1710_ = lean_ctor_get(v_cfg_1694_, 1);
lean_inc(v_outputsFile_x3f_1710_);
if (lean_obj_tag(v_outputsFile_x3f_1710_) == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_box(0);
v_val_1698_ = v___x_1711_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1720_; 
v_isSharedCheck_1720_ = !lean_is_exclusive(v_outputsFile_x3f_1710_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v_outputsFile_x3f_1710_, 0);
lean_dec(v_unused_1721_);
v___x_1713_ = v_outputsFile_x3f_1710_;
v_isShared_1714_ = v_isSharedCheck_1720_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v_outputsFile_x3f_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1720_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1715_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2);
v___x_1716_ = lean_st_mk_ref(v___x_1715_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1716_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v_val_1698_ = v___x_1718_;
goto v___jp_1697_;
}
}
}
v___jp_1697_:
{
lean_object* v_lakeEnv_1699_; lean_object* v___x_1700_; uint64_t v___x_1701_; uint64_t v___x_1702_; uint64_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_lakeEnv_1699_ = lean_ctor_get(v_ws_1693_, 1);
v___x_1700_ = l_Lake_Env_leanGithash(v_lakeEnv_1699_);
v___x_1701_ = l_Lake_Hash_nil;
v___x_1702_ = lean_string_hash(v___x_1700_);
v___x_1703_ = lean_uint64_mix_hash(v___x_1701_, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_1705_ = lean_string_append(v___x_1704_, v___x_1700_);
lean_dec_ref(v___x_1700_);
v___x_1706_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
v___x_1707_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_1708_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1708_, 0, v___x_1705_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
lean_ctor_set(v___x_1708_, 2, v___x_1707_);
lean_ctor_set_uint64(v___x_1708_, sizeof(void*)*3, v___x_1703_);
v___x_1709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1709_, 0, v_cfg_1694_);
lean_ctor_set(v___x_1709_, 1, v_ws_1693_);
lean_ctor_set(v___x_1709_, 2, v___x_1708_);
lean_ctor_set(v___x_1709_, 3, v_jobs_1695_);
lean_ctor_set(v___x_1709_, 4, v_val_1698_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(lean_object* v_ws_1722_, lean_object* v_cfg_1723_, lean_object* v_jobs_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_1722_, v_cfg_1723_, v_jobs_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_log_1735_; uint8_t v_action_1736_; uint8_t v_wantsRebuild_1737_; lean_object* v_trace_1738_; lean_object* v_buildTime_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1768_; 
v_log_1735_ = lean_ctor_get(v___y_1733_, 0);
v_action_1736_ = lean_ctor_get_uint8(v___y_1733_, sizeof(void*)*3);
v_wantsRebuild_1737_ = lean_ctor_get_uint8(v___y_1733_, sizeof(void*)*3 + 1);
v_trace_1738_ = lean_ctor_get(v___y_1733_, 1);
v_buildTime_1739_ = lean_ctor_get(v___y_1733_, 2);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___y_1733_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1741_ = v___y_1733_;
v_isShared_1742_ = v_isSharedCheck_1768_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_buildTime_1739_);
lean_inc(v_trace_1738_);
lean_inc(v_log_1735_);
lean_dec(v___y_1733_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1768_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_apply_7(v_build_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v_log_1735_, lean_box(0));
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1755_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_a_1745_ = lean_ctor_get(v___x_1743_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1747_ = v___x_1743_;
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_a_1745_);
v___x_1750_ = v___x_1741_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1745_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_trace_1738_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_buildTime_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*3, v_action_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1754_, sizeof(void*)*3 + 1, v_wantsRebuild_1737_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1750_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1744_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1767_; 
v_a_1756_ = lean_ctor_get(v___x_1743_, 0);
v_a_1757_ = lean_ctor_get(v___x_1743_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1759_ = v___x_1743_;
v_isShared_1760_ = v_isSharedCheck_1767_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_inc(v_a_1756_);
lean_dec(v___x_1743_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1767_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v_a_1757_);
v___x_1762_ = v___x_1741_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1757_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_trace_1738_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_buildTime_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1766_, sizeof(void*)*3, v_action_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1766_, sizeof(void*)*3 + 1, v_wantsRebuild_1737_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1762_);
v___x_1764_ = v___x_1759_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1756_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_1779_, lean_object* v_build_1780_, lean_object* v_caption_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1783_ = lean_box(1);
v___x_1784_ = lean_st_mk_ref(v___x_1783_);
v___f_1785_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1785_, 0, v_build_1780_);
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_box(0);
v___x_1789_ = lean_box(0);
v___x_1790_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
lean_inc(v___x_1784_);
v___x_1791_ = l_Lake_Job_async___redArg(v___x_1786_, v___f_1785_, v___x_1787_, v_caption_1781_, v___x_1790_, v___x_1789_, v___x_1788_, v___x_1784_, v_bctx_1779_);
v___x_1792_ = lean_st_ref_get(v___x_1784_);
lean_dec(v___x_1784_);
lean_dec(v___x_1792_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_1793_, lean_object* v_build_1794_, lean_object* v_caption_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1793_, v_build_1794_, v_caption_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_1798_, lean_object* v_bctx_1799_, lean_object* v_build_1800_, lean_object* v_caption_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1799_, v_build_1800_, v_caption_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_1804_, lean_object* v_bctx_1805_, lean_object* v_build_1806_, lean_object* v_caption_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_1804_, v_bctx_1805_, v_build_1806_, v_caption_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v___x_1810_, uint8_t v___x_1811_, uint8_t v___x_1812_, lean_object* v_as_1813_, size_t v_i_1814_, size_t v_stop_1815_, lean_object* v_b_1816_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_usize_dec_eq(v_i_1814_, v_stop_1815_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; size_t v___x_1821_; size_t v___x_1822_; 
v___x_1819_ = lean_array_uget_borrowed(v_as_1813_, v_i_1814_);
lean_inc_ref(v___x_1810_);
v___x_1820_ = l_Lake_logToStream(v___x_1819_, v___x_1810_, v___x_1811_, v___x_1812_);
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1814_, v___x_1821_);
v_i_1814_ = v___x_1822_;
v_b_1816_ = v___x_1820_;
goto _start;
}
else
{
lean_dec_ref(v___x_1810_);
return v_b_1816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v___x_1824_, lean_object* v___x_1825_, lean_object* v___x_1826_, lean_object* v_as_1827_, lean_object* v_i_1828_, lean_object* v_stop_1829_, lean_object* v_b_1830_, lean_object* v___y_1831_){
_start:
{
uint8_t v___x_1217__boxed_1832_; uint8_t v___x_1218__boxed_1833_; size_t v_i_boxed_1834_; size_t v_stop_boxed_1835_; lean_object* v_res_1836_; 
v___x_1217__boxed_1832_ = lean_unbox(v___x_1825_);
v___x_1218__boxed_1833_ = lean_unbox(v___x_1826_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1828_);
lean_dec(v_i_1828_);
v_stop_boxed_1835_ = lean_unbox_usize(v_stop_1829_);
lean_dec(v_stop_1829_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_1824_, v___x_1217__boxed_1832_, v___x_1218__boxed_1833_, v_as_1827_, v_i_boxed_1834_, v_stop_boxed_1835_, v_b_1830_);
lean_dec_ref(v_as_1827_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_1837_, uint8_t v___x_1838_, uint8_t v___x_1839_, lean_object* v_ws_1840_, lean_object* v_outputsRef_x3f_1841_, lean_object* v_out_1842_, lean_object* v_outputsFile_1843_, uint8_t v_isVerbose_1844_){
_start:
{
lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___x_1942_; 
v___x_1942_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1840_);
if (v___x_1942_ == 0)
{
lean_object* v_root_1943_; lean_object* v_baseName_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_root_1943_ = lean_ctor_get(v_ws_1840_, 0);
lean_inc_ref(v_root_1943_);
lean_dec_ref(v_ws_1840_);
v_baseName_1944_ = lean_ctor_get(v_root_1943_, 1);
lean_inc(v_baseName_1944_);
lean_dec_ref(v_root_1943_);
v___x_1945_ = l_Lean_Name_toString(v_baseName_1944_, v___x_1942_);
v___x_1946_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
v___x_1947_ = lean_string_append(v___x_1945_, v___x_1946_);
v___x_1948_ = 2;
v___x_1949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*1, v___x_1948_);
lean_inc_ref(v___x_1837_);
v___x_1950_ = l_Lake_logToStream(v___x_1949_, v___x_1837_, v___x_1838_, v___x_1839_);
lean_dec_ref(v___x_1949_);
goto v___jp_1875_;
}
else
{
lean_dec_ref(v_ws_1840_);
goto v___jp_1875_;
}
v___jp_1846_:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
v___jp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = lean_array_get_size(v___y_1850_);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_nat_dec_lt(v___y_1849_, v___x_1851_);
if (v___x_1853_ == 0)
{
lean_dec_ref(v___y_1850_);
lean_dec_ref(v___x_1837_);
return v___x_1852_;
}
else
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_nat_dec_le(v___x_1851_, v___x_1851_);
if (v___x_1854_ == 0)
{
if (v___x_1853_ == 0)
{
lean_dec_ref(v___y_1850_);
lean_dec_ref(v___x_1837_);
return v___x_1852_;
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1851_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_1837_, v___x_1838_, v___x_1839_, v___y_1850_, v___x_1855_, v___x_1856_, v___x_1852_);
lean_dec_ref(v___y_1850_);
return v___x_1857_;
}
}
else
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)0ULL);
v___x_1859_ = lean_usize_of_nat(v___x_1851_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_1837_, v___x_1838_, v___x_1839_, v___y_1850_, v___x_1858_, v___x_1859_, v___x_1852_);
lean_dec_ref(v___y_1850_);
return v___x_1860_;
}
}
}
v___jp_1861_:
{
if (v_isVerbose_1844_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___x_1837_);
v___x_1864_ = lean_box(0);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1865_ = lean_array_get_size(v___y_1863_);
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_nat_dec_lt(v___y_1862_, v___x_1865_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___x_1837_);
return v___x_1866_;
}
else
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_nat_dec_le(v___x_1865_, v___x_1865_);
if (v___x_1868_ == 0)
{
if (v___x_1867_ == 0)
{
lean_dec_ref(v___y_1863_);
lean_dec_ref(v___x_1837_);
return v___x_1866_;
}
else
{
size_t v___x_1869_; size_t v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = lean_usize_of_nat(v___x_1865_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_1837_, v___x_1838_, v___x_1839_, v___y_1863_, v___x_1869_, v___x_1870_, v___x_1866_);
lean_dec_ref(v___y_1863_);
return v___x_1871_;
}
}
else
{
size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((size_t)0ULL);
v___x_1873_ = lean_usize_of_nat(v___x_1865_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_1837_, v___x_1838_, v___x_1839_, v___y_1863_, v___x_1872_, v___x_1873_, v___x_1866_);
lean_dec_ref(v___y_1863_);
return v___x_1874_;
}
}
}
}
v___jp_1875_:
{
if (lean_obj_tag(v_outputsRef_x3f_1841_) == 1)
{
lean_object* v_val_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_val_1876_ = lean_ctor_get(v_outputsRef_x3f_1841_, 0);
v___x_1877_ = lean_st_ref_get(v_val_1876_);
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1880_ = l_Lake_CacheMap_writeFile(v_outputsFile_1843_, v___x_1877_, v___x_1879_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 1);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = lean_array_get_size(v_a_1881_);
v___x_1883_ = lean_nat_dec_eq(v___x_1882_, v___x_1878_);
if (v___x_1883_ == 0)
{
if (v_isVerbose_1844_ == 0)
{
lean_dec(v_a_1881_);
lean_dec_ref(v_out_1842_);
lean_dec_ref(v___x_1837_);
goto v___jp_1846_;
}
else
{
lean_object* v_putStr_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_putStr_1884_ = lean_ctor_get(v_out_1842_, 4);
lean_inc_ref(v_putStr_1884_);
lean_dec_ref(v_out_1842_);
v___x_1885_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1886_ = lean_apply_2(v_putStr_1884_, v___x_1885_, lean_box(0));
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_dec_ref(v___x_1886_);
v___y_1849_ = v___x_1878_;
v___y_1850_ = v_a_1881_;
goto v___jp_1848_;
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1889_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1890_ = lean_unsigned_to_nat(89u);
v___x_1891_ = lean_unsigned_to_nat(4u);
v___x_1892_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
v___x_1893_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
v___x_1894_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1893_, v_isVerbose_1844_);
v___x_1895_ = lean_string_append(v___x_1892_, v___x_1894_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
v___x_1897_ = lean_string_append(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_io_error_to_string(v_a_1887_);
v___x_1899_ = lean_string_append(v___x_1897_, v___x_1898_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1901_ = lean_string_append(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
v___x_1903_ = lean_string_append(v___x_1901_, v___x_1902_);
v___x_1904_ = l_mkPanicMessageWithDecl(v___x_1888_, v___x_1889_, v___x_1890_, v___x_1891_, v___x_1903_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1904_);
v___y_1849_ = v___x_1878_;
v___y_1850_ = v_a_1881_;
goto v___jp_1848_;
}
}
}
else
{
lean_dec(v_a_1881_);
lean_dec_ref(v_out_1842_);
lean_dec_ref(v___x_1837_);
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v_putStr_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1906_ = lean_ctor_get(v___x_1880_, 1);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1880_);
v_putStr_1907_ = lean_ctor_get(v_out_1842_, 4);
lean_inc_ref(v_putStr_1907_);
lean_dec_ref(v_out_1842_);
v___x_1908_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1909_ = lean_apply_2(v_putStr_1907_, v___x_1908_, lean_box(0));
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_dec_ref(v___x_1909_);
v___y_1862_ = v___x_1878_;
v___y_1863_ = v_a_1906_;
goto v___jp_1861_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___x_1909_);
v___x_1911_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1912_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1913_ = lean_unsigned_to_nat(89u);
v___x_1914_ = lean_unsigned_to_nat(4u);
v___x_1915_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1916_ = lean_io_error_to_string(v_a_1910_);
v___x_1917_ = lean_string_append(v___x_1915_, v___x_1916_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1919_ = lean_string_append(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
v___x_1921_ = lean_string_append(v___x_1919_, v___x_1920_);
v___x_1922_ = l_mkPanicMessageWithDecl(v___x_1911_, v___x_1912_, v___x_1913_, v___x_1914_, v___x_1921_);
lean_dec_ref(v___x_1921_);
v___x_1923_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1922_);
v___y_1862_ = v___x_1878_;
v___y_1863_ = v_a_1906_;
goto v___jp_1861_;
}
}
}
else
{
lean_object* v_putStr_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_outputsFile_1843_);
lean_dec_ref(v___x_1837_);
v_putStr_1924_ = lean_ctor_get(v_out_1842_, 4);
lean_inc_ref(v_putStr_1924_);
lean_dec_ref(v_out_1842_);
v___x_1925_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
v___x_1926_ = lean_apply_2(v_putStr_1924_, v___x_1925_, lean_box(0));
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
return v_a_1927_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1928_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1926_);
v___x_1929_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1930_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1931_ = lean_unsigned_to_nat(89u);
v___x_1932_ = lean_unsigned_to_nat(4u);
v___x_1933_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
v___x_1934_ = lean_io_error_to_string(v_a_1928_);
v___x_1935_ = lean_string_append(v___x_1933_, v___x_1934_);
lean_dec_ref(v___x_1934_);
v___x_1936_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
v___x_1937_ = lean_string_append(v___x_1935_, v___x_1936_);
v___x_1938_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
v___x_1939_ = lean_string_append(v___x_1937_, v___x_1938_);
v___x_1940_ = l_mkPanicMessageWithDecl(v___x_1929_, v___x_1930_, v___x_1931_, v___x_1932_, v___x_1939_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1940_);
return v___x_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_1951_, lean_object* v___x_1952_, lean_object* v___x_1953_, lean_object* v_ws_1954_, lean_object* v_outputsRef_x3f_1955_, lean_object* v_out_1956_, lean_object* v_outputsFile_1957_, lean_object* v_isVerbose_1958_, lean_object* v_a_1959_){
_start:
{
uint8_t v___x_1385__boxed_1960_; uint8_t v___x_1386__boxed_1961_; uint8_t v_isVerbose_boxed_1962_; lean_object* v_res_1963_; 
v___x_1385__boxed_1960_ = lean_unbox(v___x_1952_);
v___x_1386__boxed_1961_ = lean_unbox(v___x_1953_);
v_isVerbose_boxed_1962_ = lean_unbox(v_isVerbose_1958_);
v_res_1963_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_1951_, v___x_1385__boxed_1960_, v___x_1386__boxed_1961_, v_ws_1954_, v_outputsRef_x3f_1955_, v_out_1956_, v_outputsFile_1957_, v_isVerbose_boxed_1962_);
lean_dec(v_outputsRef_x3f_1955_);
return v_res_1963_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = 3;
v___x_1965_ = lean_uint32_to_uint8(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_1966_, lean_object* v_bctx_1967_, lean_object* v_mctx_1968_, lean_object* v_result_1969_){
_start:
{
lean_object* v___y_1972_; lean_object* v_out_1975_; uint8_t v_outLv_1976_; uint8_t v_useAnsi_1977_; lean_object* v_toMonitorResult_1978_; lean_object* v_out_1979_; lean_object* v___x_1980_; uint8_t v_noBuild_1981_; uint8_t v_verbosity_1982_; lean_object* v_outputsFile_x3f_1983_; 
v_out_1975_ = lean_ctor_get(v_mctx_1968_, 1);
lean_inc_ref(v_out_1975_);
v_outLv_1976_ = lean_ctor_get_uint8(v_mctx_1968_, sizeof(void*)*3);
v_useAnsi_1977_ = lean_ctor_get_uint8(v_mctx_1968_, sizeof(void*)*3 + 4);
lean_dec_ref(v_mctx_1968_);
v_toMonitorResult_1978_ = lean_ctor_get(v_result_1969_, 0);
lean_inc_ref(v_toMonitorResult_1978_);
v_out_1979_ = lean_ctor_get(v_result_1969_, 1);
lean_inc_ref(v_out_1979_);
lean_dec_ref(v_result_1969_);
lean_inc_ref(v_toMonitorResult_1978_);
lean_inc_ref(v_out_1975_);
v___x_1980_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1966_, v_out_1975_, v_toMonitorResult_1978_);
v_noBuild_1981_ = lean_ctor_get_uint8(v_cfg_1966_, sizeof(void*)*2 + 2);
v_verbosity_1982_ = lean_ctor_get_uint8(v_cfg_1966_, sizeof(void*)*2 + 3);
v_outputsFile_x3f_1983_ = lean_ctor_get(v_cfg_1966_, 1);
lean_inc(v_outputsFile_x3f_1983_);
lean_dec_ref(v_cfg_1966_);
if (lean_obj_tag(v_outputsFile_x3f_1983_) == 1)
{
lean_object* v_val_1998_; lean_object* v_toContext_1999_; lean_object* v_outputsRef_x3f_2000_; uint8_t v___y_2002_; 
v_val_1998_ = lean_ctor_get(v_outputsFile_x3f_1983_, 0);
lean_inc(v_val_1998_);
lean_dec_ref(v_outputsFile_x3f_1983_);
v_toContext_1999_ = lean_ctor_get(v_bctx_1967_, 1);
lean_inc(v_toContext_1999_);
v_outputsRef_x3f_2000_ = lean_ctor_get(v_bctx_1967_, 4);
lean_inc(v_outputsRef_x3f_2000_);
lean_dec_ref(v_bctx_1967_);
if (v_verbosity_1982_ == 2)
{
uint8_t v___x_2004_; 
v___x_2004_ = 1;
v___y_2002_ = v___x_2004_;
goto v___jp_2001_;
}
else
{
uint8_t v___x_2005_; 
v___x_2005_ = 0;
v___y_2002_ = v___x_2005_;
goto v___jp_2001_;
}
v___jp_2001_:
{
lean_object* v___x_2003_; 
lean_inc_ref(v_out_1975_);
v___x_2003_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_1975_, v_outLv_1976_, v_useAnsi_1977_, v_toContext_1999_, v_outputsRef_x3f_2000_, v_out_1975_, v_val_1998_, v___y_2002_);
lean_dec(v_outputsRef_x3f_2000_);
goto v___jp_1984_;
}
}
else
{
lean_dec(v_outputsFile_x3f_1983_);
lean_dec_ref(v_out_1975_);
lean_dec_ref(v_bctx_1967_);
goto v___jp_1984_;
}
v___jp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_mk_io_user_error(v___y_1972_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
v___jp_1984_:
{
if (lean_obj_tag(v_out_1979_) == 0)
{
if (v_noBuild_1981_ == 0)
{
lean_object* v_a_1985_; 
lean_dec_ref(v_toMonitorResult_1978_);
v_a_1985_ = lean_ctor_get(v_out_1979_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v_out_1979_);
v___y_1972_ = v_a_1985_;
goto v___jp_1971_;
}
else
{
uint8_t v_wantsRebuild_1986_; 
v_wantsRebuild_1986_ = lean_ctor_get_uint8(v_toMonitorResult_1978_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_1978_);
if (v_wantsRebuild_1986_ == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v_out_1979_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v_out_1979_);
v___y_1972_ = v_a_1987_;
goto v___jp_1971_;
}
else
{
uint8_t v___x_1988_; lean_object* v___x_1989_; 
lean_dec_ref(v_out_1979_);
v___x_1988_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_1989_ = lean_io_exit(v___x_1988_);
return v___x_1989_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v_toMonitorResult_1978_);
v_a_1990_ = lean_ctor_get(v_out_1979_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_out_1979_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v_out_1979_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v_out_1979_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 0);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2006_, lean_object* v_bctx_2007_, lean_object* v_mctx_2008_, lean_object* v_result_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2006_, v_bctx_2007_, v_mctx_2008_, v_result_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2012_, lean_object* v_cfg_2013_, lean_object* v_bctx_2014_, lean_object* v_mctx_2015_, lean_object* v_result_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2013_, v_bctx_2014_, v_mctx_2015_, v_result_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_cfg_2020_, lean_object* v_bctx_2021_, lean_object* v_mctx_2022_, lean_object* v_result_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2019_, v_cfg_2020_, v_bctx_2021_, v_mctx_2022_, v_result_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2026_, lean_object* v_build_2027_, lean_object* v_cfg_2028_, lean_object* v_caption_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2031_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2032_ = lean_st_mk_ref(v___x_2031_);
lean_inc(v___x_2032_);
v___x_2033_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2028_, v___x_2032_);
lean_inc_ref(v_cfg_2028_);
v___x_2034_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2026_, v_cfg_2028_, v___x_2032_);
lean_inc_ref(v___x_2034_);
v___x_2035_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2034_, v_build_2027_, v_caption_2029_);
lean_inc_ref(v___x_2033_);
v___x_2036_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2033_, v___x_2035_);
v___x_2037_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2028_, v___x_2034_, v___x_2033_, v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2038_, lean_object* v_build_2039_, lean_object* v_cfg_2040_, lean_object* v_caption_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2038_, v_build_2039_, v_cfg_2040_, v_caption_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2044_, lean_object* v_ws_2045_, lean_object* v_build_2046_, lean_object* v_cfg_2047_, lean_object* v_caption_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2045_, v_build_2046_, v_cfg_2047_, v_caption_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2051_, lean_object* v_ws_2052_, lean_object* v_build_2053_, lean_object* v_cfg_2054_, lean_object* v_caption_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2051_, v_ws_2052_, v_build_2053_, v_cfg_2054_, v_caption_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2061_, lean_object* v_job_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v_out_2065_; 
v___x_2064_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2061_, v_job_2062_);
v_out_2065_ = lean_ctor_get(v___x_2064_, 1);
lean_inc_ref(v_out_2065_);
if (lean_obj_tag(v_out_2065_) == 0)
{
lean_object* v_toMonitorResult_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2081_; 
v_toMonitorResult_2066_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2064_, 1);
lean_dec(v_unused_2082_);
v___x_2068_ = v___x_2064_;
v_isShared_2069_ = v_isSharedCheck_2081_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_toMonitorResult_2066_);
lean_dec(v___x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2081_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2080_; 
v_a_2070_ = lean_ctor_get(v_out_2065_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_out_2065_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2072_ = v_out_2065_;
v_isShared_2073_ = v_isSharedCheck_2080_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v_out_2065_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2080_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2075_);
v___x_2077_ = v___x_2068_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_toMonitorResult_2066_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2106_; 
v_a_2083_ = lean_ctor_get(v_out_2065_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_out_2065_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2085_ = v_out_2065_;
v_isShared_2086_ = v_isSharedCheck_2106_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v_out_2065_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2106_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_toMonitorResult_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2104_; 
v_toMonitorResult_2087_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v___x_2064_, 1);
lean_dec(v_unused_2105_);
v___x_2089_ = v___x_2064_;
v_isShared_2090_ = v_isSharedCheck_2104_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_toMonitorResult_2087_);
lean_dec(v___x_2064_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2104_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_task_2091_; lean_object* v___x_2092_; 
v_task_2091_ = lean_ctor_get(v_a_2083_, 0);
lean_inc_ref(v_task_2091_);
lean_dec(v_a_2083_);
v___x_2092_ = lean_io_wait(v_task_2091_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_a_2093_);
v___x_2095_ = v___x_2085_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v___x_2095_);
v___x_2097_ = v___x_2089_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_toMonitorResult_2087_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2092_);
lean_del_object(v___x_2085_);
v___x_2100_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v___x_2100_);
v___x_2102_ = v___x_2089_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_toMonitorResult_2087_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2107_, lean_object* v_job_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2107_, v_job_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2111_, lean_object* v_mctx_2112_, lean_object* v_job_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2112_, v_job_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_mctx_2117_, lean_object* v_job_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2116_, v_mctx_2117_, v_job_2118_);
return v_res_2120_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2133_, lean_object* v_build_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_out_2146_; 
v___x_2136_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2137_ = lean_st_mk_ref(v___x_2136_);
v___x_2138_ = 0;
v___x_2139_ = 1;
v___x_2140_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2137_);
v___x_2141_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2140_, v___x_2137_);
v___x_2142_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2133_, v___x_2140_, v___x_2137_);
v___x_2143_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2144_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2142_, v_build_2134_, v___x_2143_);
v___x_2145_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2141_, v___x_2144_);
v_out_2146_ = lean_ctor_get(v___x_2145_, 1);
lean_inc_ref(v_out_2146_);
lean_dec_ref(v___x_2145_);
if (lean_obj_tag(v_out_2146_) == 0)
{
lean_dec_ref(v_out_2146_);
return v___x_2138_;
}
else
{
lean_dec_ref(v_out_2146_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2147_, lean_object* v_build_2148_, lean_object* v_a_2149_){
_start:
{
uint8_t v_res_2150_; lean_object* v_r_2151_; 
v_res_2150_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2147_, v_build_2148_);
v_r_2151_ = lean_box(v_res_2150_);
return v_r_2151_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2152_, lean_object* v_ws_2153_, lean_object* v_build_2154_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2153_, v_build_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2157_, lean_object* v_ws_2158_, lean_object* v_build_2159_, lean_object* v_a_2160_){
_start:
{
uint8_t v_res_2161_; lean_object* v_r_2162_; 
v_res_2161_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2157_, v_ws_2158_, v_build_2159_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2163_, lean_object* v_build_2164_, lean_object* v_cfg_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2167_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2168_ = lean_st_mk_ref(v___x_2167_);
lean_inc(v___x_2168_);
v___x_2169_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2165_, v___x_2168_);
lean_inc_ref(v_cfg_2165_);
v___x_2170_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2163_, v_cfg_2165_, v___x_2168_);
v___x_2171_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
lean_inc_ref(v___x_2170_);
v___x_2172_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2170_, v_build_2164_, v___x_2171_);
lean_inc_ref(v___x_2169_);
v___x_2173_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2169_, v___x_2172_);
v___x_2174_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2165_, v___x_2170_, v___x_2169_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2175_, lean_object* v_build_2176_, lean_object* v_cfg_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lake_Workspace_runBuild___redArg(v_ws_2175_, v_build_2176_, v_cfg_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2180_, lean_object* v_ws_2181_, lean_object* v_build_2182_, lean_object* v_cfg_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lake_Workspace_runBuild___redArg(v_ws_2181_, v_build_2182_, v_cfg_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2186_, lean_object* v_ws_2187_, lean_object* v_build_2188_, lean_object* v_cfg_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lake_Workspace_runBuild(v_00_u03b1_2186_, v_ws_2187_, v_build_2188_, v_cfg_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2192_, lean_object* v_cfg_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lake_Workspace_runBuild___redArg(v_a_2194_, v_build_2192_, v_cfg_2193_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2197_, lean_object* v_cfg_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lake_runBuild___redArg(v_build_2197_, v_cfg_2198_, v_a_2199_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2202_, lean_object* v_build_2203_, lean_object* v_cfg_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lake_Workspace_runBuild___redArg(v_a_2205_, v_build_2203_, v_cfg_2204_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_build_2209_, lean_object* v_cfg_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lake_runBuild(v_00_u03b1_2208_, v_build_2209_, v_cfg_2210_, v_a_2211_);
return v_res_2213_;
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
