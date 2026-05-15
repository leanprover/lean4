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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
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
extern lean_object* l_instMonadBaseIO;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\033[2K\r"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Build.Run"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "_private.Lake.Build.Run.0.Lake.print!"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Build"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value),LEAN_SCALAR_PTR_LITERAL(2, 137, 78, 165, 26, 100, 189, 141)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Run"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__10 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value),LEAN_SCALAR_PTR_LITERAL(54, 210, 138, 215, 143, 190, 184, 44)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__11 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(223, 16, 116, 91, 164, 49, 31, 222)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__12 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 129, 2, 182, 107, 115, 87, 113)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__13 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "print!"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__14 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value),LEAN_SCALAR_PTR_LITERAL(171, 56, 2, 158, 131, 186, 32, 163)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__15 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__16;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " failed: "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__18 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__19;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__20 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_mkBuildContext___closed__0_value),((lean_object*)&l_Lake_mkBuildContext___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value;
static const lean_array_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = ": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_value;
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
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Nothing to build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__6;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__7;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__8;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Some required targets logged failures:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__9_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__10;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__11;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__12;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_Workspace_checkNoBuild___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 0, 0, 0, 0)}};
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
v_lakeEnv_21_ = lean_ctor_get(v_ws_16_, 0);
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
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_box(0);
v___x_126_ = l_instMonadBaseIO;
v___x_127_ = l_instInhabitedOfMonad___redArg(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16(void){
_start:
{
uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = 1;
v___x_158_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__16, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16);
v___x_161_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_162_ = lean_string_append(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_165_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__17, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
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
v___x_178_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_179_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_180_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_181_ = lean_unsigned_to_nat(89u);
v___x_182_ = lean_unsigned_to_nat(4u);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_185_ = lean_io_error_to_string(v_a_174_);
v___x_186_ = lean_string_append(v___x_184_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
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
v_putStr_212_ = lean_ctor_get(v_out_211_, 4);
lean_inc_ref(v_putStr_212_);
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
v___x_219_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_220_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_221_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_222_ = lean_unsigned_to_nat(89u);
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_226_ = lean_io_error_to_string(v_a_215_);
v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
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
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_645__overap_237_; lean_object* v___x_238_; 
v___x_233_ = l_Std_Format_defWidth;
v___x_234_ = l_Std_Format_pretty(v___x_232_, v___x_233_, v___x_224_, v___x_224_);
v___x_235_ = lean_string_append(v___x_229_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = l_mkPanicMessageWithDecl(v___x_220_, v___x_221_, v___x_222_, v___x_223_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_645__overap_237_ = l_panic___redArg(v___x_219_, v___x_236_);
v___x_238_ = lean_apply_1(v___x_645__overap_237_, lean_box(0));
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
lean_dec_ref(v_a_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_val_250_; lean_object* v_out_252_; lean_object* v_flush_253_; lean_object* v___x_254_; 
v_out_252_ = lean_ctor_get(v_a_246_, 1);
v_flush_253_ = lean_ctor_get(v_out_252_, 0);
lean_inc_ref(v_flush_253_);
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
lean_dec_ref(v_a_257_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* v_msg_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_8556__overap_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_8556__overap_264_ = lean_panic_fn_borrowed(v___x_263_, v_msg_261_);
v___x_265_ = lean_apply_1(v___x_8556__overap_264_, lean_box(0));
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
goto v___jp_282_;
}
else
{
uint8_t v_useAnsi_286_; 
v_useAnsi_286_ = lean_ctor_get_uint8(v_a_279_, sizeof(void*)*3 + 4);
if (v_useAnsi_286_ == 0)
{
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
v___x_298_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_299_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
v___x_300_ = lean_array_fget_borrowed(v___x_298_, v_spinnerIdx_293_);
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
v___x_329_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
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
v___x_337_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_339_ = lean_unsigned_to_nat(89u);
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_343_, v_useAnsi_286_);
v___x_345_ = lean_string_append(v___x_341_, v___x_344_);
lean_dec_ref(v___x_344_);
v___x_346_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
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
lean_dec_ref(v_a_385_);
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
lean_dec_ref(v_a_399_);
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
uint8_t v___y_16424__boxed_458_; uint8_t v_useAnsi_16425__boxed_459_; size_t v_i_boxed_460_; size_t v_stop_boxed_461_; lean_object* v_res_462_; 
v___y_16424__boxed_458_ = lean_unbox(v___y_450_);
v_useAnsi_16425__boxed_459_ = lean_unbox(v_useAnsi_451_);
v_i_boxed_460_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_449_, v___y_16424__boxed_458_, v_useAnsi_16425__boxed_459_, v_as_452_, v_i_boxed_460_, v_stop_boxed_461_, v_b_455_, v___y_456_);
lean_dec_ref(v_as_452_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___y_475_; lean_object* v___y_479_; lean_object* v_val_480_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_jobNo_494_; lean_object* v_totalJobs_495_; uint8_t v_wantsRebuild_496_; lean_object* v_failures_497_; lean_object* v_resetCtrl_498_; lean_object* v_lastUpdate_499_; lean_object* v_spinnerIdx_500_; lean_object* v_out_501_; uint8_t v_outLv_502_; uint8_t v_failLv_503_; uint8_t v_minAction_504_; uint8_t v_showOptional_505_; uint8_t v_useAnsi_506_; uint8_t v_showProgress_507_; uint8_t v_showTime_508_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; uint8_t v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; uint8_t v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v_task_610_; lean_object* v_caption_611_; uint8_t v_optional_612_; lean_object* v___y_614_; uint32_t v___y_615_; lean_object* v___y_616_; uint8_t v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_649_; uint32_t v___y_650_; lean_object* v___y_651_; uint8_t v___y_652_; uint8_t v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; uint32_t v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___y_690_; uint8_t v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; uint32_t v___y_694_; uint8_t v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; uint8_t v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; uint8_t v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; uint8_t v___y_724_; uint8_t v___y_726_; uint8_t v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; uint8_t v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; uint8_t v___y_754_; uint8_t v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; uint8_t v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; uint8_t v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; uint8_t v___y_764_; uint8_t v___y_779_; uint8_t v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; uint8_t v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; uint8_t v___y_788_; uint8_t v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_797_; uint8_t v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; uint8_t v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; uint8_t v___y_810_; lean_object* v___y_811_; uint8_t v___y_812_; lean_object* v___y_813_; uint8_t v___y_814_; lean_object* v___y_819_; lean_object* v___x_830_; lean_object* v_a_831_; 
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
v_flush_486_ = lean_ctor_get(v_out_485_, 0);
lean_inc_ref(v_flush_486_);
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
v___x_516_ = lean_nat_dec_lt(v___y_514_, v___y_511_);
lean_dec(v___y_514_);
if (v___x_516_ == 0)
{
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
v___y_483_ = v___y_512_;
v___y_484_ = v___y_513_;
goto v___jp_482_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_nat_dec_le(v___y_511_, v___y_511_);
if (v___x_518_ == 0)
{
if (v___x_516_ == 0)
{
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
v___y_483_ = v___y_512_;
v___y_484_ = v___y_513_;
goto v___jp_482_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___y_511_);
lean_dec(v___y_511_);
lean_inc_ref(v_out_501_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_501_, v___y_515_, v_useAnsi_506_, v___y_510_, v___x_519_, v___x_520_, v___x_517_, v___y_513_);
lean_dec_ref(v___y_510_);
v___y_491_ = v___y_512_;
v___y_492_ = v___x_521_;
goto v___jp_490_;
}
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___y_511_);
lean_dec(v___y_511_);
lean_inc_ref(v_out_501_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_501_, v___y_515_, v_useAnsi_506_, v___y_510_, v___x_522_, v___x_523_, v___x_517_, v___y_513_);
lean_dec_ref(v___y_510_);
v___y_491_ = v___y_512_;
v___y_492_ = v___x_524_;
goto v___jp_490_;
}
}
}
v___jp_525_:
{
if (v___y_530_ == 0)
{
lean_dec(v___y_532_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
v___y_483_ = v___y_528_;
v___y_484_ = v___y_531_;
goto v___jp_482_;
}
else
{
if (v___y_529_ == 0)
{
v___y_510_ = v___y_527_;
v___y_511_ = v___y_526_;
v___y_512_ = v___y_528_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_532_;
v___y_515_ = v_outLv_502_;
goto v___jp_509_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = 0;
v___y_510_ = v___y_527_;
v___y_511_ = v___y_526_;
v___y_512_ = v___y_528_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_532_;
v___y_515_ = v___x_533_;
goto v___jp_509_;
}
}
}
v___jp_534_:
{
lean_object* v_out_544_; lean_object* v_jobNo_545_; lean_object* v_totalJobs_546_; uint8_t v_wantsRebuild_547_; lean_object* v_failures_548_; lean_object* v_resetCtrl_549_; lean_object* v_lastUpdate_550_; lean_object* v_spinnerIdx_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_597_; 
v_out_544_ = lean_ctor_get(v___y_538_, 1);
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
v___y_526_ = v___y_536_;
v___y_527_ = v___y_535_;
v___y_528_ = v___y_538_;
v___y_529_ = v___y_540_;
v___y_530_ = v___y_541_;
v___y_531_ = v___x_558_;
v___y_532_ = v___y_542_;
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
v___x_567_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_568_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_569_ = lean_unsigned_to_nat(89u);
v___x_570_ = lean_unsigned_to_nat(4u);
v___x_571_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_572_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_573_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc(v___y_542_);
v___x_574_ = l_Lean_Name_num___override(v___x_573_, v___y_542_);
v___x_575_ = l_Lean_Name_str___override(v___x_574_, v___x_572_);
v___x_576_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_577_ = l_Lean_Name_str___override(v___x_575_, v___x_576_);
v___x_578_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_577_, v___y_539_);
v___x_579_ = lean_string_append(v___x_571_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = lean_io_error_to_string(v_a_563_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
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
lean_inc_n(v___y_542_, 2);
v___x_590_ = l_Std_Format_pretty(v___x_588_, v___x_589_, v___y_542_, v___y_542_);
v___x_591_ = lean_string_append(v___x_585_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = l_mkPanicMessageWithDecl(v___x_567_, v___x_568_, v___x_569_, v___x_570_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_592_);
v___y_526_ = v___y_536_;
v___y_527_ = v___y_535_;
v___y_528_ = v___y_538_;
v___y_529_ = v___y_540_;
v___y_530_ = v___y_541_;
v___y_531_ = v___x_558_;
v___y_532_ = v___y_542_;
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
v___x_609_ = l_Lake_Ansi_chalk(v___y_608_, v___y_599_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_608_);
v___y_535_ = v___y_601_;
v___y_536_ = v___y_600_;
v___y_537_ = v___y_602_;
v___y_538_ = v___y_603_;
v___y_539_ = v___y_605_;
v___y_540_ = v___y_604_;
v___y_541_ = v___y_606_;
v___y_542_ = v___y_607_;
v___y_543_ = v___x_609_;
goto v___jp_534_;
}
v___jp_613_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_627_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_628_ = lean_string_push(v___x_627_, v___y_615_);
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
v___x_639_ = lean_string_append(v___x_638_, v___y_614_);
v___x_640_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
v___x_642_ = lean_string_append(v___x_641_, v___y_619_);
lean_dec_ref(v___y_619_);
v___x_643_ = lean_string_append(v___x_642_, v___x_640_);
v___x_644_ = lean_string_append(v___x_643_, v_caption_611_);
lean_dec_ref(v_caption_611_);
v___x_645_ = lean_string_append(v___x_644_, v___y_626_);
lean_dec_ref(v___y_626_);
if (v_useAnsi_506_ == 0)
{
v___y_535_ = v___y_621_;
v___y_536_ = v___y_620_;
v___y_537_ = v___y_616_;
v___y_538_ = v___y_623_;
v___y_539_ = v___y_618_;
v___y_540_ = v___y_617_;
v___y_541_ = v___y_624_;
v___y_542_ = v___y_625_;
v___y_543_ = v___x_645_;
goto v___jp_534_;
}
else
{
if (v___y_624_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_599_ = v___x_645_;
v___y_600_ = v___y_620_;
v___y_601_ = v___y_621_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_623_;
v___y_604_ = v___y_617_;
v___y_605_ = v___y_618_;
v___y_606_ = v___y_624_;
v___y_607_ = v___y_625_;
v___y_608_ = v___x_646_;
goto v___jp_598_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_Lake_LogLevel_ansiColor(v___y_622_);
v___y_599_ = v___x_645_;
v___y_600_ = v___y_620_;
v___y_601_ = v___y_621_;
v___y_602_ = v___y_616_;
v___y_603_ = v___y_623_;
v___y_604_ = v___y_617_;
v___y_605_ = v___y_618_;
v___y_606_ = v___y_624_;
v___y_607_ = v___y_625_;
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
lean_dec(v___y_672_);
v___y_649_ = v___y_675_;
v___y_650_ = v___y_663_;
v___y_651_ = v___y_664_;
v___y_652_ = v___y_665_;
v___y_653_ = v___y_666_;
v___y_654_ = v___y_667_;
v___y_655_ = v___y_668_;
v___y_656_ = v___y_669_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_671_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
goto v___jp_648_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_lt(v___y_674_, v___y_672_);
if (v___x_676_ == 0)
{
lean_dec(v___y_672_);
v___y_649_ = v___y_675_;
v___y_650_ = v___y_663_;
v___y_651_ = v___y_664_;
v___y_652_ = v___y_665_;
v___y_653_ = v___y_666_;
v___y_654_ = v___y_667_;
v___y_655_ = v___y_668_;
v___y_656_ = v___y_669_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_671_;
v___y_659_ = v___y_673_;
v___y_660_ = v___y_674_;
goto v___jp_648_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_678_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_672_);
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___y_614_ = v___y_675_;
v___y_615_ = v___y_663_;
v___y_616_ = v___y_664_;
v___y_617_ = v___y_665_;
v___y_618_ = v___y_666_;
v___y_619_ = v___y_667_;
v___y_620_ = v___y_668_;
v___y_621_ = v___y_669_;
v___y_622_ = v___y_670_;
v___y_623_ = v___y_671_;
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
v___y_663_ = v___y_694_;
v___y_664_ = v___y_687_;
v___y_665_ = v___y_691_;
v___y_666_ = v___y_690_;
v___y_667_ = v___y_683_;
v___y_668_ = v___y_685_;
v___y_669_ = v___y_684_;
v___y_670_ = v___y_686_;
v___y_671_ = v___y_689_;
v___y_672_ = v___y_688_;
v___y_673_ = v___y_692_;
v___y_674_ = v___y_693_;
v___y_675_ = v___x_695_;
goto v___jp_662_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_663_ = v___y_694_;
v___y_664_ = v___y_687_;
v___y_665_ = v___y_691_;
v___y_666_ = v___y_690_;
v___y_667_ = v___y_683_;
v___y_668_ = v___y_685_;
v___y_669_ = v___y_684_;
v___y_670_ = v___y_686_;
v___y_671_ = v___y_689_;
v___y_672_ = v___y_688_;
v___y_673_ = v___y_692_;
v___y_674_ = v___y_693_;
v___y_675_ = v___x_696_;
goto v___jp_662_;
}
}
v___jp_697_:
{
if (v___y_707_ == 0)
{
if (v_showProgress_507_ == 0)
{
lean_dec(v___y_708_);
lean_dec(v___y_705_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_703_;
goto v___jp_474_;
}
else
{
if (v_useAnsi_506_ == 0)
{
if (v___y_698_ == 0)
{
lean_dec(v___y_708_);
lean_dec(v___y_705_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_703_;
goto v___jp_474_;
}
else
{
lean_object* v___x_709_; uint32_t v___x_710_; 
v___x_709_ = l_Lake_JobAction_verb(v___y_706_, v___y_699_);
v___x_710_ = 10004;
v___y_683_ = v___x_709_;
v___y_684_ = v___y_700_;
v___y_685_ = v___y_701_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_703_;
v___y_688_ = v___y_705_;
v___y_689_ = v___y_704_;
v___y_690_ = v___y_698_;
v___y_691_ = v___y_706_;
v___y_692_ = v___y_707_;
v___y_693_ = v___y_708_;
v___y_694_ = v___x_710_;
goto v___jp_682_;
}
}
else
{
lean_dec(v___y_708_);
lean_dec(v___y_705_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_703_;
goto v___jp_474_;
}
}
}
else
{
lean_object* v___x_711_; uint32_t v___x_712_; 
v___x_711_ = l_Lake_JobAction_verb(v___y_706_, v___y_699_);
v___x_712_ = l_Lake_LogLevel_icon(v___y_702_);
v___y_683_ = v___x_711_;
v___y_684_ = v___y_700_;
v___y_685_ = v___y_701_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_703_;
v___y_688_ = v___y_705_;
v___y_689_ = v___y_704_;
v___y_690_ = v___y_707_;
v___y_691_ = v___y_706_;
v___y_692_ = v___y_707_;
v___y_693_ = v___y_708_;
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
v___y_702_ = v___y_719_;
v___y_703_ = v___y_718_;
v___y_704_ = v___y_720_;
v___y_705_ = v___y_721_;
v___y_706_ = v___y_722_;
v___y_707_ = v___y_724_;
v___y_708_ = v___y_723_;
goto v___jp_697_;
}
else
{
if (v_showOptional_505_ == 0)
{
lean_dec(v___y_723_);
lean_dec(v___y_721_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_475_ = v___y_718_;
goto v___jp_474_;
}
else
{
v___y_698_ = v___y_714_;
v___y_699_ = v___y_715_;
v___y_700_ = v___y_716_;
v___y_701_ = v___y_717_;
v___y_702_ = v___y_719_;
v___y_703_ = v___y_718_;
v___y_704_ = v___y_720_;
v___y_705_ = v___y_721_;
v___y_706_ = v___y_722_;
v___y_707_ = v___y_724_;
v___y_708_ = v___y_723_;
goto v___jp_697_;
}
}
}
v___jp_725_:
{
if (v___y_734_ == 0)
{
if (v___y_727_ == 0)
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_729_;
v___y_717_ = v___y_730_;
v___y_718_ = v___y_737_;
v___y_719_ = v___y_731_;
v___y_720_ = v___y_736_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_727_;
goto v___jp_713_;
}
else
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_729_;
v___y_717_ = v___y_730_;
v___y_718_ = v___y_737_;
v___y_719_ = v___y_731_;
v___y_720_ = v___y_736_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_733_;
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
v___y_715_ = v___y_728_;
v___y_716_ = v___y_729_;
v___y_717_ = v___y_730_;
v___y_718_ = v___x_750_;
v___y_719_ = v___y_731_;
v___y_720_ = v___y_736_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_734_;
goto v___jp_713_;
}
}
}
else
{
v___y_714_ = v___y_726_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_729_;
v___y_717_ = v___y_730_;
v___y_718_ = v___y_737_;
v___y_719_ = v___y_731_;
v___y_720_ = v___y_736_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_734_;
goto v___jp_713_;
}
}
}
v___jp_753_:
{
if (v___y_759_ == 0)
{
v___y_726_ = v___y_764_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_756_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
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
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*6, v___y_759_);
v___y_726_ = v___y_764_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_756_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_763_;
v___y_736_ = v_a_471_;
v___y_737_ = v___x_769_;
goto v___jp_725_;
}
}
}
else
{
v___y_726_ = v___y_764_;
v___y_727_ = v___y_754_;
v___y_728_ = v___y_755_;
v___y_729_ = v___y_756_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
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
v___x_789_ = l_Lake_instOrdJobAction_ord(v_minAction_504_, v___y_780_);
if (v___x_789_ == 2)
{
uint8_t v___x_790_; 
v___x_790_ = 0;
v___y_754_ = v___y_779_;
v___y_755_ = v___y_780_;
v___y_756_ = v___y_782_;
v___y_757_ = v___y_781_;
v___y_758_ = v___y_783_;
v___y_759_ = v___y_785_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_788_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_787_;
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
v___y_759_ = v___y_785_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_788_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_787_;
v___y_764_ = v___x_791_;
goto v___jp_753_;
}
}
v___jp_792_:
{
uint8_t v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_strict_and(v___y_793_, v___y_801_);
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
v___y_784_ = v___y_799_;
v___y_785_ = v___y_798_;
v___y_786_ = v___x_802_;
v___y_787_ = v___y_800_;
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
v___y_784_ = v___y_799_;
v___y_785_ = v___y_798_;
v___y_786_ = v___x_802_;
v___y_787_ = v___y_800_;
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
v___y_793_ = v___y_814_;
v___y_794_ = v___y_807_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_808_;
v___y_797_ = v___y_810_;
v___y_798_ = v___y_812_;
v___y_799_ = v___y_811_;
v___y_800_ = v___y_813_;
v___y_801_ = v___x_816_;
goto v___jp_792_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 1;
v___y_793_ = v___y_814_;
v___y_794_ = v___y_807_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_808_;
v___y_797_ = v___y_810_;
v___y_798_ = v___y_812_;
v___y_799_ = v___y_811_;
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
v___y_807_ = v_action_821_;
v___y_808_ = v___x_825_;
v___y_809_ = v_log_820_;
v___y_810_ = v___x_824_;
v___y_811_ = v_buildTime_823_;
v___y_812_ = v_wantsRebuild_822_;
v___y_813_ = v___x_826_;
v___y_814_ = v___x_828_;
goto v___jp_806_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = 0;
v___y_807_ = v_action_821_;
v___y_808_ = v___x_825_;
v___y_809_ = v_log_820_;
v___y_810_ = v___x_824_;
v___y_811_ = v_buildTime_823_;
v___y_812_ = v_wantsRebuild_822_;
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
lean_dec_ref(v_a_833_);
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
uint8_t v___y_17198__boxed_858_; uint8_t v_useAnsi_17199__boxed_859_; size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v___y_17198__boxed_858_ = lean_unbox(v___y_849_);
v_useAnsi_17199__boxed_859_ = lean_unbox(v_useAnsi_850_);
v_i_boxed_860_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_848_, v___y_17198__boxed_858_, v_useAnsi_17199__boxed_859_, v_as_851_, v_i_boxed_860_, v_stop_boxed_861_, v_b_854_, v___y_855_, v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v_as_851_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_jobs_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_jobNo_870_; lean_object* v_totalJobs_871_; uint8_t v_wantsRebuild_872_; lean_object* v_failures_873_; lean_object* v_resetCtrl_874_; lean_object* v_lastUpdate_875_; lean_object* v_spinnerIdx_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_886_; 
v_jobs_866_ = lean_ctor_get(v_a_863_, 0);
v___x_867_ = lean_st_ref_take(v_jobs_866_);
v___x_868_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_869_ = lean_st_ref_set(v_jobs_866_, v___x_868_);
v_jobNo_870_ = lean_ctor_get(v_a_864_, 0);
v_totalJobs_871_ = lean_ctor_get(v_a_864_, 1);
v_wantsRebuild_872_ = lean_ctor_get_uint8(v_a_864_, sizeof(void*)*6);
v_failures_873_ = lean_ctor_get(v_a_864_, 2);
v_resetCtrl_874_ = lean_ctor_get(v_a_864_, 3);
v_lastUpdate_875_ = lean_ctor_get(v_a_864_, 4);
v_spinnerIdx_876_ = lean_ctor_get(v_a_864_, 5);
v_isSharedCheck_886_ = !lean_is_exclusive(v_a_864_);
if (v_isSharedCheck_886_ == 0)
{
v___x_878_ = v_a_864_;
v_isShared_879_ = v_isSharedCheck_886_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_spinnerIdx_876_);
lean_inc(v_lastUpdate_875_);
lean_inc(v_resetCtrl_874_);
lean_inc(v_failures_873_);
lean_inc(v_totalJobs_871_);
lean_inc(v_jobNo_870_);
lean_dec(v_a_864_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_886_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = lean_array_get_size(v___x_867_);
v___x_881_ = lean_nat_add(v_totalJobs_871_, v___x_880_);
lean_dec(v_totalJobs_871_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v___x_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_jobNo_870_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_failures_873_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_resetCtrl_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_lastUpdate_875_);
lean_ctor_set(v_reuseFailAlloc_885_, 5, v_spinnerIdx_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_885_, sizeof(void*)*6, v_wantsRebuild_872_);
v___x_883_ = v_reuseFailAlloc_885_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_867_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_887_, v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object* v_as_891_, size_t v_i_892_, size_t v_stop_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_fst_899_; lean_object* v_snd_900_; uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_eq(v_i_892_, v_stop_893_);
if (v___x_904_ == 0)
{
lean_object* v_fst_905_; lean_object* v_snd_906_; lean_object* v___x_907_; lean_object* v_task_908_; uint8_t v___x_909_; 
v_fst_905_ = lean_ctor_get(v_b_894_, 0);
v_snd_906_ = lean_ctor_get(v_b_894_, 1);
v___x_907_ = lean_array_uget_borrowed(v_as_891_, v_i_892_);
v_task_908_ = lean_ctor_get(v___x_907_, 0);
v___x_909_ = lean_io_get_task_state(v_task_908_);
switch(v___x_909_)
{
case 0:
{
lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_917_; 
lean_inc(v_snd_906_);
lean_inc(v_fst_905_);
v_isSharedCheck_917_ = !lean_is_exclusive(v_b_894_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; 
v_unused_918_ = lean_ctor_get(v_b_894_, 1);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_b_894_, 0);
lean_dec(v_unused_919_);
v___x_911_ = v_b_894_;
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
else
{
lean_dec(v_b_894_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_917_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_inc(v___x_907_);
v___x_913_ = lean_array_push(v_snd_906_, v___x_907_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v_fst_899_ = v___x_915_;
v_snd_900_ = v___y_896_;
goto v___jp_898_;
}
}
}
case 1:
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_928_; 
lean_inc(v_snd_906_);
lean_inc(v_fst_905_);
v_isSharedCheck_928_ = !lean_is_exclusive(v_b_894_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; lean_object* v_unused_930_; 
v_unused_929_ = lean_ctor_get(v_b_894_, 1);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_b_894_, 0);
lean_dec(v_unused_930_);
v___x_921_ = v_b_894_;
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
else
{
lean_dec(v_b_894_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
lean_inc_n(v___x_907_, 2);
v___x_923_ = lean_array_push(v_fst_905_, v___x_907_);
v___x_924_ = lean_array_push(v_snd_906_, v___x_907_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_924_);
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v_fst_899_ = v___x_926_;
v_snd_900_ = v___y_896_;
goto v___jp_898_;
}
}
}
default: 
{
lean_object* v___x_931_; lean_object* v_snd_932_; lean_object* v_jobNo_933_; lean_object* v_totalJobs_934_; uint8_t v_wantsRebuild_935_; lean_object* v_failures_936_; lean_object* v_resetCtrl_937_; lean_object* v_lastUpdate_938_; lean_object* v_spinnerIdx_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
lean_inc(v___x_907_);
v___x_931_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_907_, v___y_895_, v___y_896_);
v_snd_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc(v_snd_932_);
lean_dec_ref(v___x_931_);
v_jobNo_933_ = lean_ctor_get(v_snd_932_, 0);
v_totalJobs_934_ = lean_ctor_get(v_snd_932_, 1);
v_wantsRebuild_935_ = lean_ctor_get_uint8(v_snd_932_, sizeof(void*)*6);
v_failures_936_ = lean_ctor_get(v_snd_932_, 2);
v_resetCtrl_937_ = lean_ctor_get(v_snd_932_, 3);
v_lastUpdate_938_ = lean_ctor_get(v_snd_932_, 4);
v_spinnerIdx_939_ = lean_ctor_get(v_snd_932_, 5);
v_isSharedCheck_948_ = !lean_is_exclusive(v_snd_932_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v_snd_932_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_spinnerIdx_939_);
lean_inc(v_lastUpdate_938_);
lean_inc(v_resetCtrl_937_);
lean_inc(v_failures_936_);
lean_inc(v_totalJobs_934_);
lean_inc(v_jobNo_933_);
lean_dec(v_snd_932_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_jobNo_933_, v___x_943_);
lean_dec(v_jobNo_933_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_totalJobs_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_failures_936_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_resetCtrl_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_lastUpdate_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v_spinnerIdx_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*6, v_wantsRebuild_935_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
v_fst_899_ = v_b_894_;
v_snd_900_ = v___x_946_;
goto v___jp_898_;
}
}
}
}
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_b_894_);
lean_ctor_set(v___x_949_, 1, v___y_896_);
return v___x_949_;
}
v___jp_898_:
{
size_t v___x_901_; size_t v___x_902_; 
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_892_, v___x_901_);
v_i_892_ = v___x_902_;
v_b_894_ = v_fst_899_;
v___y_896_ = v_snd_900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object* v_as_950_, lean_object* v_i_951_, lean_object* v_stop_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
size_t v_i_boxed_957_; size_t v_stop_boxed_958_; lean_object* v_res_959_; 
v_i_boxed_957_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_stop_boxed_958_ = lean_unbox_usize(v_stop_952_);
lean_dec(v_stop_952_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_950_, v_i_boxed_957_, v_stop_boxed_958_, v_b_953_, v___y_954_, v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object* v_new_962_, lean_object* v_unfinished_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___y_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___y_982_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_985_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_986_ = lean_array_get_size(v_unfinished_963_);
v___x_987_ = lean_nat_dec_lt(v___x_967_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_inc_ref(v_a_965_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_985_);
lean_ctor_set(v___x_988_, 1, v_a_965_);
v___y_969_ = v___x_988_;
v_fst_970_ = v___x_985_;
v_snd_971_ = v_a_965_;
goto v___jp_968_;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_le(v___x_986_, v___x_986_);
if (v___x_989_ == 0)
{
if (v___x_987_ == 0)
{
lean_object* v___x_990_; 
lean_inc_ref(v_a_965_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_985_);
lean_ctor_set(v___x_990_, 1, v_a_965_);
v___y_969_ = v___x_990_;
v_fst_970_ = v___x_985_;
v_snd_971_ = v_a_965_;
goto v___jp_968_;
}
else
{
size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_of_nat(v___x_986_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_963_, v___x_991_, v___x_992_, v___x_985_, v_a_964_, v_a_965_);
v___y_982_ = v___x_993_;
goto v___jp_981_;
}
}
else
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)0ULL);
v___x_995_ = lean_usize_of_nat(v___x_986_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_963_, v___x_994_, v___x_995_, v___x_985_, v_a_964_, v_a_965_);
v___y_982_ = v___x_996_;
goto v___jp_981_;
}
}
v___jp_968_:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_array_get_size(v_new_962_);
v___x_973_ = lean_nat_dec_lt(v___x_967_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec_ref(v_snd_971_);
lean_dec_ref(v_fst_970_);
return v___y_969_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_le(v___x_972_, v___x_972_);
if (v___x_974_ == 0)
{
if (v___x_973_ == 0)
{
lean_dec_ref(v_snd_971_);
lean_dec_ref(v_fst_970_);
return v___y_969_;
}
else
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
lean_dec_ref(v___y_969_);
v___x_975_ = ((size_t)0ULL);
v___x_976_ = lean_usize_of_nat(v___x_972_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_962_, v___x_975_, v___x_976_, v_fst_970_, v_a_964_, v_snd_971_);
return v___x_977_;
}
}
else
{
size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v___y_969_);
v___x_978_ = ((size_t)0ULL);
v___x_979_ = lean_usize_of_nat(v___x_972_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_962_, v___x_978_, v___x_979_, v_fst_970_, v_a_964_, v_snd_971_);
return v___x_980_;
}
}
}
v___jp_981_:
{
lean_object* v_fst_983_; lean_object* v_snd_984_; 
v_fst_983_ = lean_ctor_get(v___y_982_, 0);
lean_inc(v_fst_983_);
v_snd_984_ = lean_ctor_get(v___y_982_, 1);
lean_inc(v_snd_984_);
v___y_969_ = v___y_982_;
v_fst_970_ = v_fst_983_;
v_snd_971_ = v_snd_984_;
goto v___jp_968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_997_, lean_object* v_unfinished_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_997_, v_unfinished_998_, v_a_999_, v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_unfinished_998_);
lean_dec_ref(v_new_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___y_1007_; lean_object* v___x_1025_; lean_object* v_lastUpdate_1026_; lean_object* v_updateFrequency_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1025_ = lean_io_mono_ms_now();
v_lastUpdate_1026_ = lean_ctor_get(v_a_1004_, 4);
v_updateFrequency_1027_ = lean_ctor_get(v_a_1003_, 2);
v___x_1028_ = lean_nat_sub(v___x_1025_, v_lastUpdate_1026_);
lean_dec(v___x_1025_);
v___x_1029_ = lean_nat_sub(v_updateFrequency_1027_, v___x_1028_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_nat_dec_lt(v___x_1030_, v___x_1029_);
if (v___x_1031_ == 0)
{
lean_dec(v___x_1029_);
v___y_1007_ = v_a_1004_;
goto v___jp_1006_;
}
else
{
uint32_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_uint32_of_nat(v___x_1029_);
lean_dec(v___x_1029_);
v___x_1033_ = l_IO_sleep(v___x_1032_);
v___y_1007_ = v_a_1004_;
goto v___jp_1006_;
}
v___jp_1006_:
{
lean_object* v___x_1008_; lean_object* v_jobNo_1009_; lean_object* v_totalJobs_1010_; uint8_t v_wantsRebuild_1011_; lean_object* v_failures_1012_; lean_object* v_resetCtrl_1013_; lean_object* v_spinnerIdx_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1023_; 
v___x_1008_ = lean_io_mono_ms_now();
v_jobNo_1009_ = lean_ctor_get(v___y_1007_, 0);
v_totalJobs_1010_ = lean_ctor_get(v___y_1007_, 1);
v_wantsRebuild_1011_ = lean_ctor_get_uint8(v___y_1007_, sizeof(void*)*6);
v_failures_1012_ = lean_ctor_get(v___y_1007_, 2);
v_resetCtrl_1013_ = lean_ctor_get(v___y_1007_, 3);
v_spinnerIdx_1014_ = lean_ctor_get(v___y_1007_, 5);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___y_1007_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v___y_1007_, 4);
lean_dec(v_unused_1024_);
v___x_1016_ = v___y_1007_;
v_isShared_1017_ = v_isSharedCheck_1023_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_spinnerIdx_1014_);
lean_inc(v_resetCtrl_1013_);
lean_inc(v_failures_1012_);
lean_inc(v_totalJobs_1010_);
lean_inc(v_jobNo_1009_);
lean_dec(v___y_1007_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1023_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 4, v___x_1008_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_jobNo_1009_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_totalJobs_1010_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_failures_1012_);
lean_ctor_set(v_reuseFailAlloc_1022_, 3, v_resetCtrl_1013_);
lean_ctor_set(v_reuseFailAlloc_1022_, 4, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1022_, 5, v_spinnerIdx_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, sizeof(void*)*6, v_wantsRebuild_1011_);
v___x_1020_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1018_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1034_, v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_1038_, lean_object* v_unfinished_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1043_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1038_, v_unfinished_1039_, v_a_1040_, v_a_1041_);
lean_dec_ref(v_unfinished_1039_);
lean_dec_ref(v_new_1038_);
v_fst_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_fst_1044_);
v_snd_1045_ = lean_ctor_get(v___x_1043_, 1);
lean_inc(v_snd_1045_);
lean_dec_ref(v___x_1043_);
v_fst_1046_ = lean_ctor_get(v_fst_1044_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v_fst_1044_, 1);
lean_inc(v_snd_1047_);
lean_dec(v_fst_1044_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_array_get_size(v_snd_1047_);
v___x_1050_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_fst_1046_);
v___x_1051_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1040_, v_snd_1045_);
v_fst_1052_ = lean_ctor_get(v___x_1051_, 0);
v_snd_1053_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1055_ = v___x_1051_;
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snd_1053_);
lean_inc(v_fst_1052_);
lean_dec(v___x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1064_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_array_get_size(v_fst_1052_);
v___x_1058_ = lean_nat_dec_lt(v___x_1048_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec(v_fst_1052_);
lean_dec(v_snd_1047_);
v___x_1059_ = lean_box(0);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1059_);
v___x_1061_ = v___x_1055_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_snd_1053_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_del_object(v___x_1055_);
v_new_1038_ = v_fst_1052_;
v_unfinished_1039_ = v_snd_1047_;
v_a_1041_ = v_snd_1053_;
goto _start;
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v_snd_1066_; lean_object* v___x_1067_; lean_object* v_snd_1068_; lean_object* v___x_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; 
v___x_1065_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1046_, v_snd_1047_, v_a_1040_, v_snd_1045_);
lean_dec(v_fst_1046_);
v_snd_1066_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_snd_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1040_, v_snd_1066_);
v_snd_1068_ = lean_ctor_get(v___x_1067_, 1);
lean_inc(v_snd_1068_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1040_, v_snd_1068_);
v_fst_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_fst_1070_);
v_snd_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_snd_1071_);
lean_dec_ref(v___x_1069_);
v_new_1038_ = v_fst_1070_;
v_unfinished_1039_ = v_snd_1047_;
v_a_1041_ = v_snd_1071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1073_, lean_object* v_unfinished_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1073_, v_unfinished_1074_, v_a_1075_, v_a_1076_);
lean_dec_ref(v_a_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1154_; 
v___x_1083_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1080_, v_a_1081_);
v_fst_1084_ = lean_ctor_get(v___x_1083_, 0);
v_snd_1085_ = lean_ctor_get(v___x_1083_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1087_ = v___x_1083_;
v_isShared_1088_ = v_isSharedCheck_1154_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snd_1085_);
lean_inc(v_fst_1084_);
lean_dec(v___x_1083_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1154_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v_snd_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1152_; 
v___x_1089_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1084_, v_init_1079_, v_a_1080_, v_snd_1085_);
v_snd_1090_ = lean_ctor_get(v___x_1089_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1153_);
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1152_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_snd_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1152_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_jobNo_1094_; lean_object* v_totalJobs_1095_; uint8_t v_wantsRebuild_1096_; lean_object* v_failures_1097_; lean_object* v_resetCtrl_1098_; lean_object* v_lastUpdate_1099_; lean_object* v_spinnerIdx_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1151_; 
v_jobNo_1094_ = lean_ctor_get(v_snd_1090_, 0);
v_totalJobs_1095_ = lean_ctor_get(v_snd_1090_, 1);
v_wantsRebuild_1096_ = lean_ctor_get_uint8(v_snd_1090_, sizeof(void*)*6);
v_failures_1097_ = lean_ctor_get(v_snd_1090_, 2);
v_resetCtrl_1098_ = lean_ctor_get(v_snd_1090_, 3);
v_lastUpdate_1099_ = lean_ctor_get(v_snd_1090_, 4);
v_spinnerIdx_1100_ = lean_ctor_get(v_snd_1090_, 5);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_snd_1090_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1102_ = v_snd_1090_;
v_isShared_1103_ = v_isSharedCheck_1151_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_spinnerIdx_1100_);
lean_inc(v_lastUpdate_1099_);
lean_inc(v_resetCtrl_1098_);
lean_inc(v_failures_1097_);
lean_inc(v_totalJobs_1095_);
lean_inc(v_jobNo_1094_);
lean_dec(v_snd_1090_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1151_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 3, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_jobNo_1094_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_totalJobs_1095_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_failures_1097_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_lastUpdate_1099_);
lean_ctor_set(v_reuseFailAlloc_1150_, 5, v_spinnerIdx_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1150_, sizeof(void*)*6, v_wantsRebuild_1096_);
v___x_1106_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v_val_1108_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_string_utf8_byte_size(v_resetCtrl_1098_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_nat_dec_eq(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v_out_1115_; lean_object* v_flush_1116_; lean_object* v_putStr_1117_; lean_object* v___x_1122_; 
lean_del_object(v___x_1087_);
v_out_1115_ = lean_ctor_get(v_a_1080_, 1);
v_flush_1116_ = lean_ctor_get(v_out_1115_, 0);
v_putStr_1117_ = lean_ctor_get(v_out_1115_, 4);
lean_inc_ref(v_putStr_1117_);
lean_inc_ref(v_resetCtrl_1098_);
v___x_1122_ = lean_apply_2(v_putStr_1117_, v_resetCtrl_1098_, lean_box(0));
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_dec_ref(v___x_1122_);
lean_dec_ref(v_resetCtrl_1098_);
goto v___jp_1118_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1145_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1145_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1145_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1127_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1128_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1129_ = lean_unsigned_to_nat(89u);
v___x_1130_ = lean_unsigned_to_nat(4u);
v___x_1131_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1132_ = lean_io_error_to_string(v_a_1123_);
v___x_1133_ = lean_string_append(v___x_1131_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1135_ = lean_string_append(v___x_1133_, v___x_1134_);
v___x_1136_ = l_String_quote(v_resetCtrl_1098_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 3);
lean_ctor_set(v___x_1125_, 0, v___x_1136_);
v___x_1138_ = v___x_1125_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1139_ = l_Std_Format_defWidth;
v___x_1140_ = l_Std_Format_pretty(v___x_1138_, v___x_1139_, v___x_1113_, v___x_1113_);
v___x_1141_ = lean_string_append(v___x_1135_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = l_mkPanicMessageWithDecl(v___x_1127_, v___x_1128_, v___x_1129_, v___x_1130_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1142_);
goto v___jp_1118_;
}
}
}
v___jp_1118_:
{
lean_object* v___x_1119_; 
lean_inc_ref(v_flush_1116_);
v___x_1119_ = lean_apply_1(v_flush_1116_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1119_);
v_val_1108_ = v_a_1120_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1121_; 
lean_dec_ref(v___x_1119_);
v___x_1121_ = lean_box(0);
v_val_1108_ = v___x_1121_;
goto v___jp_1107_;
}
}
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec_ref(v_resetCtrl_1098_);
lean_del_object(v___x_1092_);
v___x_1146_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v___x_1106_);
lean_ctor_set(v___x_1087_, 0, v___x_1146_);
v___x_1148_ = v___x_1087_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1106_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
v___jp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v___x_1106_);
lean_ctor_set(v___x_1092_, 0, v_val_1108_);
v___x_1110_ = v___x_1092_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_val_1108_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1106_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1155_, v_a_1156_, v_a_1157_);
lean_dec_ref(v_a_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1160_){
_start:
{
lean_object* v_failures_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_failures_1161_ = lean_ctor_get(v_self_1160_, 0);
v___x_1162_ = lean_array_get_size(v_failures_1161_);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_nat_dec_eq(v___x_1162_, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1165_);
lean_dec_ref(v_self_1165_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1168_, lean_object* v_jobs_1169_){
_start:
{
lean_object* v_toLogConfig_1171_; uint8_t v_verbosity_1172_; uint8_t v_failLv_1173_; uint8_t v_outLv_1174_; uint8_t v_ansiMode_1175_; lean_object* v_out_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; uint8_t v___x_1180_; uint8_t v___x_1181_; uint8_t v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1188_; 
v_toLogConfig_1171_ = lean_ctor_get(v_cfg_1168_, 0);
v_verbosity_1172_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*3 + 3);
v_failLv_1173_ = lean_ctor_get_uint8(v_toLogConfig_1171_, sizeof(void*)*1);
v_outLv_1174_ = lean_ctor_get_uint8(v_toLogConfig_1171_, sizeof(void*)*1 + 1);
v_ansiMode_1175_ = lean_ctor_get_uint8(v_toLogConfig_1171_, sizeof(void*)*1 + 2);
v_out_1176_ = lean_ctor_get(v_toLogConfig_1171_, 0);
v___x_1177_ = l_Lake_OutStream_get(v_out_1176_);
lean_inc_ref(v___x_1177_);
v___x_1178_ = l_Lake_AnsiMode_isEnabled(v___x_1177_, v_ansiMode_1175_);
v___x_1179_ = l_Lake_BuildConfig_showProgress(v_cfg_1168_);
v___x_1180_ = 2;
v___x_1181_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1172_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 3;
v___y_1188_ = v___x_1190_;
goto v___jp_1187_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = 0;
v___y_1188_ = v___x_1191_;
goto v___jp_1187_;
}
v___jp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_unsigned_to_nat(100u);
v___x_1186_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v___x_1186_, 0, v_jobs_1169_);
lean_ctor_set(v___x_1186_, 1, v___x_1177_);
lean_ctor_set(v___x_1186_, 2, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3, v_outLv_1174_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3 + 1, v_failLv_1173_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3 + 2, v___y_1183_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3 + 3, v___x_1181_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3 + 4, v___x_1178_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3 + 5, v___x_1179_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3 + 6, v___y_1184_);
return v___x_1186_;
}
v___jp_1187_:
{
if (v___x_1181_ == 0)
{
if (v___x_1178_ == 0)
{
uint8_t v___x_1189_; 
v___x_1189_ = 1;
v___y_1183_ = v___y_1188_;
v___y_1184_ = v___x_1189_;
goto v___jp_1182_;
}
else
{
v___y_1183_ = v___y_1188_;
v___y_1184_ = v___x_1181_;
goto v___jp_1182_;
}
}
else
{
v___y_1183_ = v___y_1188_;
v___y_1184_ = v___x_1181_;
goto v___jp_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1192_, lean_object* v_jobs_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1192_, v_jobs_1193_);
lean_dec_ref(v_cfg_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1196_, lean_object* v_initJobs_1197_, lean_object* v_initFailures_1198_, lean_object* v_resetCtrl_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_snd_1206_; lean_object* v_totalJobs_1207_; uint8_t v_wantsRebuild_1208_; lean_object* v_failures_1209_; lean_object* v___x_1210_; 
v___x_1201_ = lean_io_mono_ms_now();
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = 0;
v___x_1204_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1202_);
lean_ctor_set(v___x_1204_, 2, v_initFailures_1198_);
lean_ctor_set(v___x_1204_, 3, v_resetCtrl_1199_);
lean_ctor_set(v___x_1204_, 4, v___x_1201_);
lean_ctor_set(v___x_1204_, 5, v___x_1202_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*6, v___x_1203_);
v___x_1205_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1197_, v_ctx_1196_, v___x_1204_);
v_snd_1206_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_snd_1206_);
lean_dec_ref(v___x_1205_);
v_totalJobs_1207_ = lean_ctor_get(v_snd_1206_, 1);
lean_inc(v_totalJobs_1207_);
v_wantsRebuild_1208_ = lean_ctor_get_uint8(v_snd_1206_, sizeof(void*)*6);
v_failures_1209_ = lean_ctor_get(v_snd_1206_, 2);
lean_inc_ref(v_failures_1209_);
lean_dec(v_snd_1206_);
v___x_1210_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1210_, 0, v_failures_1209_);
lean_ctor_set(v___x_1210_, 1, v_totalJobs_1207_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*2, v_wantsRebuild_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1211_, lean_object* v_initJobs_1212_, lean_object* v_initFailures_1213_, lean_object* v_resetCtrl_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1211_, v_initJobs_1212_, v_initFailures_1213_, v_resetCtrl_1214_);
lean_dec_ref(v_ctx_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1217_, lean_object* v_jobs_1218_, lean_object* v_out_1219_, uint8_t v_failLv_1220_, uint8_t v_outLv_1221_, uint8_t v_minAction_1222_, uint8_t v_showOptional_1223_, uint8_t v_useAnsi_1224_, uint8_t v_showProgress_1225_, uint8_t v_showTime_1226_, lean_object* v_resetCtrl_1227_, lean_object* v_initFailures_1228_, lean_object* v_updateFrequency_1229_){
_start:
{
lean_object* v_ctx_1231_; lean_object* v___x_1232_; 
v_ctx_1231_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v_ctx_1231_, 0, v_jobs_1218_);
lean_ctor_set(v_ctx_1231_, 1, v_out_1219_);
lean_ctor_set(v_ctx_1231_, 2, v_updateFrequency_1229_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3, v_outLv_1221_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3 + 1, v_failLv_1220_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3 + 2, v_minAction_1222_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3 + 3, v_showOptional_1223_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3 + 4, v_useAnsi_1224_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3 + 5, v_showProgress_1225_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*3 + 6, v_showTime_1226_);
v___x_1232_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1231_, v_initJobs_1217_, v_initFailures_1228_, v_resetCtrl_1227_);
lean_dec_ref(v_ctx_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1233_, lean_object* v_jobs_1234_, lean_object* v_out_1235_, lean_object* v_failLv_1236_, lean_object* v_outLv_1237_, lean_object* v_minAction_1238_, lean_object* v_showOptional_1239_, lean_object* v_useAnsi_1240_, lean_object* v_showProgress_1241_, lean_object* v_showTime_1242_, lean_object* v_resetCtrl_1243_, lean_object* v_initFailures_1244_, lean_object* v_updateFrequency_1245_, lean_object* v_a_1246_){
_start:
{
uint8_t v_failLv_boxed_1247_; uint8_t v_outLv_boxed_1248_; uint8_t v_minAction_boxed_1249_; uint8_t v_showOptional_boxed_1250_; uint8_t v_useAnsi_boxed_1251_; uint8_t v_showProgress_boxed_1252_; uint8_t v_showTime_boxed_1253_; lean_object* v_res_1254_; 
v_failLv_boxed_1247_ = lean_unbox(v_failLv_1236_);
v_outLv_boxed_1248_ = lean_unbox(v_outLv_1237_);
v_minAction_boxed_1249_ = lean_unbox(v_minAction_1238_);
v_showOptional_boxed_1250_ = lean_unbox(v_showOptional_1239_);
v_useAnsi_boxed_1251_ = lean_unbox(v_useAnsi_1240_);
v_showProgress_boxed_1252_ = lean_unbox(v_showProgress_1241_);
v_showTime_boxed_1253_ = lean_unbox(v_showTime_1242_);
v_res_1254_ = l_Lake_monitorJobs(v_initJobs_1233_, v_jobs_1234_, v_out_1235_, v_failLv_boxed_1247_, v_outLv_boxed_1248_, v_minAction_boxed_1249_, v_showOptional_boxed_1250_, v_useAnsi_boxed_1251_, v_showProgress_boxed_1252_, v_showTime_boxed_1253_, v_resetCtrl_1243_, v_initFailures_1244_, v_updateFrequency_1245_);
return v_res_1254_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1255_; 
v___x_1255_ = 3;
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_apply_2(v_logger_1256_, v___y_1258_, lean_box(0));
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1261_, v_x_1262_, v___y_1263_);
return v_res_1265_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___f_1267_; 
v___x_1266_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_1267_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1267_, 0, v___x_1266_);
return v___f_1267_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1275_ = l_String_quote(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
v___x_1277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = l_Std_Format_defWidth;
v___x_1280_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5);
v___x_1281_ = l_Std_Format_pretty(v___x_1280_, v___x_1279_, v___x_1278_, v___x_1278_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7));
v___x_1284_ = l_String_quote(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
v___x_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = l_Std_Format_defWidth;
v___x_1289_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_1290_ = l_Std_Format_pretty(v___x_1289_, v___x_1288_, v___x_1287_, v___x_1287_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11));
v___x_1293_ = l_String_quote(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
v___x_1295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = l_Std_Format_defWidth;
v___x_1298_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_1299_ = l_Std_Format_pretty(v___x_1298_, v___x_1297_, v___x_1296_, v___x_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1301_, lean_object* v_ws_1302_, lean_object* v_outputsRef_x3f_1303_, lean_object* v_out_1304_, lean_object* v_outputsFile_1305_, uint8_t v_isVerbose_1306_){
_start:
{
lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1328_; lean_object* v___y_1329_; uint8_t v___x_1424_; 
lean_inc_ref(v_logger_1301_);
v___f_1310_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1310_, 0, v_logger_1301_);
v___x_1311_ = l_instMonadBaseIO;
v___x_1424_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1302_);
if (v___x_1424_ == 0)
{
lean_object* v_packages_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_baseName_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_packages_1425_ = lean_ctor_get(v_ws_1302_, 4);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_array_fget_borrowed(v_packages_1425_, v___x_1426_);
v_baseName_1428_ = lean_ctor_get(v___x_1427_, 1);
lean_inc(v_baseName_1428_);
v___x_1429_ = l_Lean_Name_toString(v_baseName_1428_, v___x_1424_);
v___x_1430_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15));
v___x_1431_ = lean_string_append(v___x_1429_, v___x_1430_);
v___x_1432_ = 2;
v___x_1433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*1, v___x_1432_);
v___x_1434_ = lean_apply_2(v_logger_1301_, v___x_1433_, lean_box(0));
goto v___jp_1343_;
}
else
{
lean_dec_ref(v_logger_1301_);
goto v___jp_1343_;
}
v___jp_1308_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
v___jp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = lean_array_get_size(v___y_1313_);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_nat_dec_lt(v___y_1314_, v___x_1315_);
if (v___x_1317_ == 0)
{
lean_dec_ref(v___y_1313_);
lean_dec_ref(v___f_1310_);
return v___x_1316_;
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_nat_dec_le(v___x_1315_, v___x_1315_);
if (v___x_1318_ == 0)
{
if (v___x_1317_ == 0)
{
lean_dec_ref(v___y_1313_);
lean_dec_ref(v___f_1310_);
return v___x_1316_;
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1971__overap_1321_; lean_object* v___x_1322_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1315_);
v___x_1971__overap_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1311_, v___f_1310_, v___y_1313_, v___x_1319_, v___x_1320_, v___x_1316_);
v___x_1322_ = lean_apply_1(v___x_1971__overap_1321_, lean_box(0));
return v___x_1322_;
}
}
else
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1975__overap_1325_; lean_object* v___x_1326_; 
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = lean_usize_of_nat(v___x_1315_);
v___x_1975__overap_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1311_, v___f_1310_, v___y_1313_, v___x_1323_, v___x_1324_, v___x_1316_);
v___x_1326_ = lean_apply_1(v___x_1975__overap_1325_, lean_box(0));
return v___x_1326_;
}
}
}
v___jp_1327_:
{
if (v_isVerbose_1306_ == 0)
{
lean_object* v___x_1330_; 
lean_dec_ref(v___y_1328_);
lean_dec_ref(v___f_1310_);
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = lean_array_get_size(v___y_1328_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_nat_dec_lt(v___y_1329_, v___x_1331_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v___y_1328_);
lean_dec_ref(v___f_1310_);
return v___x_1332_;
}
else
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_nat_dec_le(v___x_1331_, v___x_1331_);
if (v___x_1334_ == 0)
{
if (v___x_1333_ == 0)
{
lean_dec_ref(v___y_1328_);
lean_dec_ref(v___f_1310_);
return v___x_1332_;
}
else
{
size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1875__overap_1337_; lean_object* v___x_1338_; 
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = lean_usize_of_nat(v___x_1331_);
v___x_1875__overap_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1311_, v___f_1310_, v___y_1328_, v___x_1335_, v___x_1336_, v___x_1332_);
v___x_1338_ = lean_apply_1(v___x_1875__overap_1337_, lean_box(0));
return v___x_1338_;
}
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1879__overap_1341_; lean_object* v___x_1342_; 
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = lean_usize_of_nat(v___x_1331_);
v___x_1879__overap_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1311_, v___f_1310_, v___y_1328_, v___x_1339_, v___x_1340_, v___x_1332_);
v___x_1342_ = lean_apply_1(v___x_1879__overap_1341_, lean_box(0));
return v___x_1342_;
}
}
}
}
v___jp_1343_:
{
if (lean_obj_tag(v_outputsRef_x3f_1303_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1345_; lean_object* v_packages_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_config_1349_; lean_object* v_toLeanConfig_1350_; lean_object* v_platformIndependent_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_val_1344_ = lean_ctor_get(v_outputsRef_x3f_1303_, 0);
v___x_1345_ = lean_st_ref_get(v_val_1344_);
v_packages_1346_ = lean_ctor_get(v_ws_1302_, 4);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_fget_borrowed(v_packages_1346_, v___x_1347_);
v_config_1349_ = lean_ctor_get(v___x_1348_, 6);
v_toLeanConfig_1350_ = lean_ctor_get(v_config_1349_, 1);
v_platformIndependent_1351_ = lean_ctor_get(v_toLeanConfig_1350_, 10);
v___f_1352_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0);
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
lean_inc(v_platformIndependent_1351_);
v___x_1354_ = l_Option_instBEq_beq___redArg(v___f_1352_, v_platformIndependent_1351_, v___x_1353_);
v___x_1355_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_1356_ = l_Lake_CacheMap_writeFile(v_outputsFile_1305_, v___x_1345_, v___x_1354_, v___x_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 1);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_array_get_size(v_a_1357_);
v___x_1359_ = lean_nat_dec_eq(v___x_1358_, v___x_1347_);
if (v___x_1359_ == 0)
{
if (v_isVerbose_1306_ == 0)
{
lean_dec(v_a_1357_);
lean_dec_ref(v___f_1310_);
lean_dec_ref(v_out_1304_);
goto v___jp_1308_;
}
else
{
lean_object* v_putStr_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_putStr_1360_ = lean_ctor_get(v_out_1304_, 4);
lean_inc_ref(v_putStr_1360_);
lean_dec_ref(v_out_1304_);
v___x_1361_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1362_ = lean_apply_2(v_putStr_1360_, v___x_1361_, lean_box(0));
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_dec_ref(v___x_1362_);
v___y_1313_ = v_a_1357_;
v___y_1314_ = v___x_1347_;
goto v___jp_1312_;
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_2113__overap_1382_; lean_object* v___x_1383_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1365_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1366_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1367_ = lean_unsigned_to_nat(89u);
v___x_1368_ = lean_unsigned_to_nat(4u);
v___x_1369_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1370_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1370_, v_isVerbose_1306_);
v___x_1372_ = lean_string_append(v___x_1369_, v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_io_error_to_string(v_a_1363_);
v___x_1376_ = lean_string_append(v___x_1374_, v___x_1375_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1380_ = lean_string_append(v___x_1378_, v___x_1379_);
v___x_1381_ = l_mkPanicMessageWithDecl(v___x_1365_, v___x_1366_, v___x_1367_, v___x_1368_, v___x_1380_);
lean_dec_ref(v___x_1380_);
v___x_2113__overap_1382_ = l_panic___redArg(v___x_1364_, v___x_1381_);
v___x_1383_ = lean_apply_1(v___x_2113__overap_1382_, lean_box(0));
v___y_1313_ = v_a_1357_;
v___y_1314_ = v___x_1347_;
goto v___jp_1312_;
}
}
}
else
{
lean_dec(v_a_1357_);
lean_dec_ref(v___f_1310_);
lean_dec_ref(v_out_1304_);
goto v___jp_1308_;
}
}
else
{
lean_object* v_a_1384_; lean_object* v_putStr_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1356_, 1);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1356_);
v_putStr_1385_ = lean_ctor_get(v_out_1304_, 4);
lean_inc_ref(v_putStr_1385_);
lean_dec_ref(v_out_1304_);
v___x_1386_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7));
v___x_1387_ = lean_apply_2(v_putStr_1385_, v___x_1386_, lean_box(0));
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_dec_ref(v___x_1387_);
v___y_1328_ = v_a_1384_;
v___y_1329_ = v___x_1347_;
goto v___jp_1327_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1770__overap_1402_; lean_object* v___x_1403_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
v___x_1389_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1390_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1391_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1392_ = lean_unsigned_to_nat(89u);
v___x_1393_ = lean_unsigned_to_nat(4u);
v___x_1394_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1395_ = lean_io_error_to_string(v_a_1388_);
v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1400_ = lean_string_append(v___x_1398_, v___x_1399_);
v___x_1401_ = l_mkPanicMessageWithDecl(v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v___x_1400_);
lean_dec_ref(v___x_1400_);
v___x_1770__overap_1402_ = l_panic___redArg(v___x_1389_, v___x_1401_);
v___x_1403_ = lean_apply_1(v___x_1770__overap_1402_, lean_box(0));
v___y_1328_ = v_a_1384_;
v___y_1329_ = v___x_1347_;
goto v___jp_1327_;
}
}
}
else
{
lean_object* v_putStr_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref(v___f_1310_);
lean_dec_ref(v_outputsFile_1305_);
v_putStr_1404_ = lean_ctor_get(v_out_1304_, 4);
lean_inc_ref(v_putStr_1404_);
lean_dec_ref(v_out_1304_);
v___x_1405_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11));
v___x_1406_ = lean_apply_2(v_putStr_1404_, v___x_1405_, lean_box(0));
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
return v_a_1407_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1925__overap_1422_; lean_object* v___x_1423_; 
v_a_1408_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1408_);
lean_dec_ref(v___x_1406_);
v___x_1409_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1410_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1411_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1412_ = lean_unsigned_to_nat(89u);
v___x_1413_ = lean_unsigned_to_nat(4u);
v___x_1414_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1415_ = lean_io_error_to_string(v_a_1408_);
v___x_1416_ = lean_string_append(v___x_1414_, v___x_1415_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
v___x_1419_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_1420_ = lean_string_append(v___x_1418_, v___x_1419_);
v___x_1421_ = l_mkPanicMessageWithDecl(v___x_1410_, v___x_1411_, v___x_1412_, v___x_1413_, v___x_1420_);
lean_dec_ref(v___x_1420_);
v___x_1925__overap_1422_ = l_panic___redArg(v___x_1409_, v___x_1421_);
v___x_1423_ = lean_apply_1(v___x_1925__overap_1422_, lean_box(0));
return v___x_1423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1435_, lean_object* v_ws_1436_, lean_object* v_outputsRef_x3f_1437_, lean_object* v_out_1438_, lean_object* v_outputsFile_1439_, lean_object* v_isVerbose_1440_, lean_object* v_a_1441_){
_start:
{
uint8_t v_isVerbose_boxed_1442_; lean_object* v_res_1443_; 
v_isVerbose_boxed_1442_ = lean_unbox(v_isVerbose_1440_);
v_res_1443_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1435_, v_ws_1436_, v_outputsRef_x3f_1437_, v_out_1438_, v_outputsFile_1439_, v_isVerbose_boxed_1442_);
lean_dec(v_outputsRef_x3f_1437_);
lean_dec_ref(v_ws_1436_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1445_, lean_object* v_as_1446_, size_t v_i_1447_, size_t v_stop_1448_, lean_object* v_b_1449_){
_start:
{
lean_object* v_val_1452_; uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_eq(v_i_1447_, v_stop_1448_);
if (v___x_1456_ == 0)
{
lean_object* v_putStr_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_putStr_1457_ = lean_ctor_get(v_out_1445_, 4);
v___x_1458_ = lean_array_uget_borrowed(v_as_1446_, v_i_1447_);
v___x_1459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1460_ = lean_string_append(v___x_1459_, v___x_1458_);
v___x_1461_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
lean_inc_ref(v_putStr_1457_);
lean_inc_ref(v___x_1462_);
v___x_1463_ = lean_apply_2(v_putStr_1457_, v___x_1462_, lean_box(0));
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; 
lean_dec_ref(v___x_1462_);
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref(v___x_1463_);
v_val_1452_ = v_a_1464_;
goto v___jp_1451_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1488_; 
v_a_1465_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1467_ = v___x_1463_;
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1469_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1470_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1471_ = lean_unsigned_to_nat(89u);
v___x_1472_ = lean_unsigned_to_nat(4u);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1475_ = lean_io_error_to_string(v_a_1465_);
v___x_1476_ = lean_string_append(v___x_1474_, v___x_1475_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
v___x_1479_ = l_String_quote(v___x_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 3);
lean_ctor_set(v___x_1467_, 0, v___x_1479_);
v___x_1481_ = v___x_1467_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1482_ = l_Std_Format_defWidth;
v___x_1483_ = l_Std_Format_pretty(v___x_1481_, v___x_1482_, v___x_1473_, v___x_1473_);
v___x_1484_ = lean_string_append(v___x_1478_, v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_mkPanicMessageWithDecl(v___x_1469_, v___x_1470_, v___x_1471_, v___x_1472_, v___x_1484_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1485_);
v_val_1452_ = v___x_1486_;
goto v___jp_1451_;
}
}
}
}
else
{
lean_dec_ref(v_out_1445_);
return v_b_1449_;
}
v___jp_1451_:
{
size_t v___x_1453_; size_t v___x_1454_; 
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1447_, v___x_1453_);
v_i_1447_ = v___x_1454_;
v_b_1449_ = v_val_1452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1489_, lean_object* v_as_1490_, lean_object* v_i_1491_, lean_object* v_stop_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_){
_start:
{
size_t v_i_boxed_1495_; size_t v_stop_boxed_1496_; lean_object* v_res_1497_; 
v_i_boxed_1495_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_stop_boxed_1496_ = lean_unbox_usize(v_stop_1492_);
lean_dec(v_stop_1492_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1489_, v_as_1490_, v_i_boxed_1495_, v_stop_boxed_1496_, v_b_1493_);
lean_dec_ref(v_as_1490_);
return v_res_1497_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1505_ = l_String_quote(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = l_Std_Format_defWidth;
v___x_1510_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1511_ = l_Std_Format_pretty(v___x_1510_, v___x_1509_, v___x_1508_, v___x_1508_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1514_ = l_String_quote(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = l_Std_Format_defWidth;
v___x_1519_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1520_ = l_Std_Format_pretty(v___x_1519_, v___x_1518_, v___x_1517_, v___x_1517_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1521_, lean_object* v_out_1522_, lean_object* v_result_1523_){
_start:
{
uint8_t v___y_1526_; lean_object* v___y_1527_; lean_object* v_failures_1601_; lean_object* v_numJobs_1602_; uint8_t v___y_1604_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_failures_1601_ = lean_ctor_get(v_result_1523_, 0);
lean_inc_ref(v_failures_1601_);
v_numJobs_1602_ = lean_ctor_get(v_result_1523_, 1);
lean_inc(v_numJobs_1602_);
lean_dec_ref(v_result_1523_);
v___x_1637_ = lean_array_get_size(v_failures_1601_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_nat_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v_flush_1640_; lean_object* v_putStr_1641_; lean_object* v___y_1647_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_numJobs_1602_);
v_flush_1640_ = lean_ctor_get(v_out_1522_, 0);
lean_inc_ref(v_flush_1640_);
v_putStr_1641_ = lean_ctor_get(v_out_1522_, 4);
v___x_1658_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1641_);
v___x_1659_ = lean_apply_2(v_putStr_1641_, v___x_1658_, lean_box(0));
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_dec_ref(v___x_1659_);
goto v___jp_1648_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1662_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1663_ = lean_unsigned_to_nat(89u);
v___x_1664_ = lean_unsigned_to_nat(4u);
v___x_1665_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1666_ = lean_io_error_to_string(v_a_1660_);
v___x_1667_ = lean_string_append(v___x_1665_, v___x_1666_);
lean_dec_ref(v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1669_ = lean_string_append(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
v___x_1672_ = l_mkPanicMessageWithDecl(v___x_1661_, v___x_1662_, v___x_1663_, v___x_1664_, v___x_1671_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1672_);
goto v___jp_1648_;
}
v___jp_1642_:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_apply_1(v_flush_1640_, lean_box(0));
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
return v_a_1644_;
}
else
{
lean_object* v___x_1645_; 
lean_dec_ref(v___x_1643_);
v___x_1645_ = lean_box(0);
return v___x_1645_;
}
}
v___jp_1646_:
{
goto v___jp_1642_;
}
v___jp_1648_:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_nat_dec_lt(v___x_1638_, v___x_1637_);
if (v___x_1649_ == 0)
{
lean_dec_ref(v_failures_1601_);
lean_dec_ref(v_out_1522_);
goto v___jp_1642_;
}
else
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_nat_dec_le(v___x_1637_, v___x_1637_);
if (v___x_1651_ == 0)
{
if (v___x_1649_ == 0)
{
lean_dec_ref(v_failures_1601_);
lean_dec_ref(v_out_1522_);
goto v___jp_1642_;
}
else
{
size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = lean_usize_of_nat(v___x_1637_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1522_, v_failures_1601_, v___x_1652_, v___x_1653_, v___x_1650_);
lean_dec_ref(v_failures_1601_);
v___y_1647_ = v___x_1654_;
goto v___jp_1646_;
}
}
else
{
size_t v___x_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = ((size_t)0ULL);
v___x_1656_ = lean_usize_of_nat(v___x_1637_);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1522_, v_failures_1601_, v___x_1655_, v___x_1656_, v___x_1650_);
lean_dec_ref(v_failures_1601_);
v___y_1647_ = v___x_1657_;
goto v___jp_1646_;
}
}
}
}
else
{
uint8_t v___x_1674_; 
lean_dec_ref(v_failures_1601_);
v___x_1674_ = l_Lake_BuildConfig_showProgress(v_cfg_1521_);
if (v___x_1674_ == 0)
{
v___y_1604_ = v___x_1674_;
goto v___jp_1603_;
}
else
{
uint8_t v_showSuccess_1675_; 
v_showSuccess_1675_ = lean_ctor_get_uint8(v_cfg_1521_, sizeof(void*)*3 + 4);
v___y_1604_ = v_showSuccess_1675_;
goto v___jp_1603_;
}
}
v___jp_1525_:
{
uint8_t v_noBuild_1528_; 
v_noBuild_1528_ = lean_ctor_get_uint8(v_cfg_1521_, sizeof(void*)*3 + 2);
if (v_noBuild_1528_ == 0)
{
lean_object* v_putStr_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_putStr_1529_ = lean_ctor_get(v_out_1522_, 4);
lean_inc_ref(v_putStr_1529_);
lean_dec_ref(v_out_1522_);
v___x_1530_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1531_ = lean_string_append(v___x_1530_, v___y_1527_);
lean_dec_ref(v___y_1527_);
v___x_1532_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1533_ = lean_string_append(v___x_1531_, v___x_1532_);
lean_inc_ref(v___x_1533_);
v___x_1534_ = lean_apply_2(v_putStr_1529_, v___x_1533_, lean_box(0));
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; 
lean_dec_ref(v___x_1533_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
return v_a_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1564_; 
v_a_1536_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1538_ = v___x_1534_;
v_isShared_1539_ = v_isSharedCheck_1564_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1564_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1540_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1541_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1542_ = lean_unsigned_to_nat(89u);
v___x_1543_ = lean_unsigned_to_nat(4u);
v___x_1544_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1547_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1546_, v___y_1526_);
v___x_1548_ = lean_string_append(v___x_1544_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1550_ = lean_string_append(v___x_1548_, v___x_1549_);
v___x_1551_ = lean_io_error_to_string(v_a_1536_);
v___x_1552_ = lean_string_append(v___x_1550_, v___x_1551_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1554_ = lean_string_append(v___x_1552_, v___x_1553_);
v___x_1555_ = l_String_quote(v___x_1533_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 3);
lean_ctor_set(v___x_1538_, 0, v___x_1555_);
v___x_1557_ = v___x_1538_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1558_ = l_Std_Format_defWidth;
v___x_1559_ = l_Std_Format_pretty(v___x_1557_, v___x_1558_, v___x_1545_, v___x_1545_);
v___x_1560_ = lean_string_append(v___x_1554_, v___x_1559_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = l_mkPanicMessageWithDecl(v___x_1540_, v___x_1541_, v___x_1542_, v___x_1543_, v___x_1560_);
lean_dec_ref(v___x_1560_);
v___x_1562_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1561_);
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_putStr_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_putStr_1565_ = lean_ctor_get(v_out_1522_, 4);
lean_inc_ref(v_putStr_1565_);
lean_dec_ref(v_out_1522_);
v___x_1566_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1567_ = lean_string_append(v___x_1566_, v___y_1527_);
lean_dec_ref(v___y_1527_);
v___x_1568_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1569_ = lean_string_append(v___x_1567_, v___x_1568_);
lean_inc_ref(v___x_1569_);
v___x_1570_ = lean_apply_2(v_putStr_1565_, v___x_1569_, lean_box(0));
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; 
lean_dec_ref(v___x_1569_);
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
return v_a_1571_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1600_; 
v_a_1572_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1574_ = v___x_1570_;
v_isShared_1575_ = v_isSharedCheck_1600_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1570_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1600_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1576_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1577_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1578_ = lean_unsigned_to_nat(89u);
v___x_1579_ = lean_unsigned_to_nat(4u);
v___x_1580_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1583_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1582_, v_noBuild_1528_);
v___x_1584_ = lean_string_append(v___x_1580_, v___x_1583_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_io_error_to_string(v_a_1572_);
v___x_1588_ = lean_string_append(v___x_1586_, v___x_1587_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1590_ = lean_string_append(v___x_1588_, v___x_1589_);
v___x_1591_ = l_String_quote(v___x_1569_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 3);
lean_ctor_set(v___x_1574_, 0, v___x_1591_);
v___x_1593_ = v___x_1574_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1594_ = l_Std_Format_defWidth;
v___x_1595_ = l_Std_Format_pretty(v___x_1593_, v___x_1594_, v___x_1581_, v___x_1581_);
v___x_1596_ = lean_string_append(v___x_1590_, v___x_1595_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = l_mkPanicMessageWithDecl(v___x_1576_, v___x_1577_, v___x_1578_, v___x_1579_, v___x_1596_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1597_);
return v___x_1598_;
}
}
}
}
}
v___jp_1603_:
{
if (v___y_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec(v_numJobs_1602_);
lean_dec_ref(v_out_1522_);
v___x_1605_ = lean_box(0);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = lean_nat_dec_eq(v_numJobs_1602_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = lean_unsigned_to_nat(1u);
v___x_1609_ = lean_nat_dec_eq(v_numJobs_1602_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = l_Nat_reprFast(v_numJobs_1602_);
v___x_1611_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
v___y_1526_ = v___y_1604_;
v___y_1527_ = v___x_1612_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1613_; 
lean_dec(v_numJobs_1602_);
v___x_1613_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1526_ = v___y_1604_;
v___y_1527_ = v___x_1613_;
goto v___jp_1525_;
}
}
else
{
lean_object* v_putStr_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_numJobs_1602_);
v_putStr_1614_ = lean_ctor_get(v_out_1522_, 4);
lean_inc_ref(v_putStr_1614_);
lean_dec_ref(v_out_1522_);
v___x_1615_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1616_ = lean_apply_2(v_putStr_1614_, v___x_1615_, lean_box(0));
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
return v_a_1617_;
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1618_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1616_);
v___x_1619_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1620_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1621_ = lean_unsigned_to_nat(89u);
v___x_1622_ = lean_unsigned_to_nat(4u);
v___x_1623_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1624_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1625_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1624_, v___x_1607_);
v___x_1626_ = lean_string_append(v___x_1623_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1628_ = lean_string_append(v___x_1626_, v___x_1627_);
v___x_1629_ = lean_io_error_to_string(v_a_1618_);
v___x_1630_ = lean_string_append(v___x_1628_, v___x_1629_);
lean_dec_ref(v___x_1629_);
v___x_1631_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1632_ = lean_string_append(v___x_1630_, v___x_1631_);
v___x_1633_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1634_ = lean_string_append(v___x_1632_, v___x_1633_);
v___x_1635_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1620_, v___x_1621_, v___x_1622_, v___x_1634_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1635_);
return v___x_1636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1676_, lean_object* v_out_1677_, lean_object* v_result_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1676_, v_out_1677_, v_result_1678_);
lean_dec_ref(v_cfg_1676_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1681_){
_start:
{
lean_object* v_toMonitorResult_1682_; 
v_toMonitorResult_1682_ = lean_ctor_get(v_self_1681_, 0);
lean_inc_ref(v_toMonitorResult_1682_);
return v_toMonitorResult_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1683_);
lean_dec_ref(v_self_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1686_){
_start:
{
lean_object* v___f_1687_; 
v___f_1687_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1687_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1688_){
_start:
{
lean_object* v_out_1689_; 
v_out_1689_ = lean_ctor_get(v_self_1688_, 1);
if (lean_obj_tag(v_out_1689_) == 0)
{
uint8_t v___x_1690_; 
v___x_1690_ = 0;
return v___x_1690_;
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = 1;
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1692_);
lean_dec_ref(v_self_1692_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1695_, lean_object* v_self_1696_){
_start:
{
lean_object* v_out_1697_; 
v_out_1697_ = lean_ctor_get(v_self_1696_, 1);
if (lean_obj_tag(v_out_1697_) == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = 0;
return v___x_1698_;
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = 1;
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_self_1701_){
_start:
{
uint8_t v_res_1702_; lean_object* v_r_1703_; 
v_res_1702_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1700_, v_self_1701_);
lean_dec_ref(v_self_1701_);
v_r_1703_ = lean_box(v_res_1702_);
return v_r_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1712_, lean_object* v_job_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_failures_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
lean_inc_ref(v_job_1713_);
v___x_1715_ = l_Lake_Job_toOpaque___redArg(v_job_1713_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_mk_empty_array_with_capacity(v___x_1716_);
v___x_1718_ = lean_array_push(v___x_1717_, v___x_1715_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1721_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1722_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1712_, v___x_1718_, v___x_1720_, v___x_1721_);
v_failures_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc_ref(v_failures_1723_);
v___x_1724_ = lean_array_get_size(v_failures_1723_);
lean_dec_ref(v_failures_1723_);
v___x_1725_ = lean_nat_dec_eq(v___x_1724_, v___x_1719_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v_job_1713_);
v___x_1726_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1722_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
return v___x_1727_;
}
else
{
lean_object* v_task_1728_; lean_object* v___x_1729_; 
v_task_1728_ = lean_ctor_get(v_job_1713_, 0);
lean_inc_ref(v_task_1728_);
lean_dec_ref(v_job_1713_);
v___x_1729_ = lean_io_wait(v_task_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1738_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; 
v_unused_1739_ = lean_ctor_get(v___x_1729_, 1);
lean_dec(v_unused_1739_);
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_a_1730_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___x_1734_);
lean_ctor_set(v___x_1732_, 0, v___x_1722_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1747_; 
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; lean_object* v_unused_1749_; 
v_unused_1748_ = lean_ctor_get(v___x_1729_, 1);
lean_dec(v_unused_1748_);
v_unused_1749_ = lean_ctor_get(v___x_1729_, 0);
lean_dec(v_unused_1749_);
v___x_1741_ = v___x_1729_;
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
else
{
lean_dec(v___x_1729_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
lean_ctor_set(v___x_1741_, 1, v___x_1743_);
lean_ctor_set(v___x_1741_, 0, v___x_1722_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1750_, lean_object* v_job_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1750_, v_job_1751_);
lean_dec_ref(v_ctx_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1754_, lean_object* v_ctx_1755_, lean_object* v_job_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1755_, v_job_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_ctx_1760_, lean_object* v_job_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1759_, v_ctx_1760_, v_job_1761_);
lean_dec_ref(v_ctx_1760_);
return v_res_1763_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_unsigned_to_nat(16u);
v___x_1768_ = lean_mk_array(v___x_1767_, v___x_1766_);
return v___x_1768_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1);
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* v_ws_1772_, lean_object* v_cfg_1773_, lean_object* v_jobs_1774_){
_start:
{
lean_object* v_val_1777_; lean_object* v_outputsFile_x3f_1789_; 
v_outputsFile_x3f_1789_ = lean_ctor_get(v_cfg_1773_, 1);
lean_inc(v_outputsFile_x3f_1789_);
if (lean_obj_tag(v_outputsFile_x3f_1789_) == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_box(0);
v_val_1777_ = v___x_1790_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1799_; 
v_isSharedCheck_1799_ = !lean_is_exclusive(v_outputsFile_x3f_1789_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v_outputsFile_x3f_1789_, 0);
lean_dec(v_unused_1800_);
v___x_1792_ = v_outputsFile_x3f_1789_;
v_isShared_1793_ = v_isSharedCheck_1799_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v_outputsFile_x3f_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1799_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1794_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2);
v___x_1795_ = lean_st_mk_ref(v___x_1794_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1795_);
v___x_1797_ = v___x_1792_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
v_val_1777_ = v___x_1797_;
goto v___jp_1776_;
}
}
}
v___jp_1776_:
{
lean_object* v_lakeEnv_1778_; lean_object* v___x_1779_; uint64_t v___x_1780_; uint64_t v___x_1781_; uint64_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_lakeEnv_1778_ = lean_ctor_get(v_ws_1772_, 0);
v___x_1779_ = l_Lake_Env_leanGithash(v_lakeEnv_1778_);
v___x_1780_ = l_Lake_Hash_nil;
v___x_1781_ = lean_string_hash(v___x_1779_);
v___x_1782_ = lean_uint64_mix_hash(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_1784_ = lean_string_append(v___x_1783_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v___x_1785_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
v___x_1786_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_1787_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1787_, 0, v___x_1784_);
lean_ctor_set(v___x_1787_, 1, v___x_1785_);
lean_ctor_set(v___x_1787_, 2, v___x_1786_);
lean_ctor_set_uint64(v___x_1787_, sizeof(void*)*3, v___x_1782_);
v___x_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1788_, 0, v_cfg_1773_);
lean_ctor_set(v___x_1788_, 1, v_ws_1772_);
lean_ctor_set(v___x_1788_, 2, v___x_1787_);
lean_ctor_set(v___x_1788_, 3, v_jobs_1774_);
lean_ctor_set(v___x_1788_, 4, v_val_1777_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(lean_object* v_ws_1801_, lean_object* v_cfg_1802_, lean_object* v_jobs_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_1801_, v_cfg_1802_, v_jobs_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_log_1814_; uint8_t v_action_1815_; uint8_t v_wantsRebuild_1816_; lean_object* v_trace_1817_; lean_object* v_buildTime_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1847_; 
v_log_1814_ = lean_ctor_get(v___y_1812_, 0);
v_action_1815_ = lean_ctor_get_uint8(v___y_1812_, sizeof(void*)*3);
v_wantsRebuild_1816_ = lean_ctor_get_uint8(v___y_1812_, sizeof(void*)*3 + 1);
v_trace_1817_ = lean_ctor_get(v___y_1812_, 1);
v_buildTime_1818_ = lean_ctor_get(v___y_1812_, 2);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___y_1812_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1820_ = v___y_1812_;
v_isShared_1821_ = v_isSharedCheck_1847_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_buildTime_1818_);
lean_inc(v_trace_1817_);
lean_inc(v_log_1814_);
lean_dec(v___y_1812_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1847_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_apply_7(v_build_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v_log_1814_, lean_box(0));
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1834_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_a_1824_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1826_ = v___x_1822_;
v_isShared_1827_ = v_isSharedCheck_1834_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1834_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1824_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1824_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_trace_1817_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_buildTime_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*3, v_action_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*3 + 1, v_wantsRebuild_1816_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1829_);
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1823_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v_a_1835_ = lean_ctor_get(v___x_1822_, 0);
v_a_1836_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1838_ = v___x_1822_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_inc(v_a_1835_);
lean_dec(v___x_1822_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1836_);
v___x_1841_ = v___x_1820_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1836_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_trace_1817_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_buildTime_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1845_, sizeof(void*)*3, v_action_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1845_, sizeof(void*)*3 + 1, v_wantsRebuild_1816_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1835_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_1858_, lean_object* v_build_1859_, lean_object* v_caption_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1862_ = lean_box(1);
v___x_1863_ = lean_st_mk_ref(v___x_1862_);
v___f_1864_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1864_, 0, v_build_1859_);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_box(0);
v___x_1869_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_1870_ = l_Lake_Job_async___redArg(v___x_1865_, v___f_1864_, v___x_1866_, v_caption_1860_, v___x_1869_, v___x_1868_, v___x_1867_, v___x_1863_, v_bctx_1858_);
v___x_1871_ = lean_st_ref_get(v___x_1863_);
lean_dec(v___x_1863_);
lean_dec(v___x_1871_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_1872_, lean_object* v_build_1873_, lean_object* v_caption_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1872_, v_build_1873_, v_caption_1874_);
lean_dec_ref(v_bctx_1872_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_1877_, lean_object* v_bctx_1878_, lean_object* v_build_1879_, lean_object* v_caption_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1878_, v_build_1879_, v_caption_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_1883_, lean_object* v_bctx_1884_, lean_object* v_build_1885_, lean_object* v_caption_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_1883_, v_bctx_1884_, v_build_1885_, v_caption_1886_);
lean_dec_ref(v_bctx_1884_);
return v_res_1888_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
if (lean_obj_tag(v_x_1889_) == 0)
{
if (lean_obj_tag(v_x_1890_) == 0)
{
uint8_t v___x_1891_; 
v___x_1891_ = 1;
return v___x_1891_;
}
else
{
uint8_t v___x_1892_; 
v___x_1892_ = 0;
return v___x_1892_;
}
}
else
{
if (lean_obj_tag(v_x_1890_) == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = 0;
return v___x_1893_;
}
else
{
lean_object* v_val_1894_; uint8_t v___x_1895_; 
v_val_1894_ = lean_ctor_get(v_x_1889_, 0);
v___x_1895_ = lean_unbox(v_val_1894_);
if (v___x_1895_ == 0)
{
lean_object* v_val_1896_; uint8_t v___x_1897_; 
v_val_1896_ = lean_ctor_get(v_x_1890_, 0);
v___x_1897_ = lean_unbox(v_val_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = 1;
return v___x_1898_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_unbox(v_val_1894_);
return v___x_1899_;
}
}
else
{
lean_object* v_val_1900_; uint8_t v___x_1901_; 
v_val_1900_ = lean_ctor_get(v_x_1890_, 0);
v___x_1901_ = lean_unbox(v_val_1900_);
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_1902_, v_x_1903_);
lean_dec(v_x_1903_);
lean_dec(v_x_1902_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_1906_, uint8_t v___x_1907_, uint8_t v___x_1908_, lean_object* v_as_1909_, size_t v_i_1910_, size_t v_stop_1911_, lean_object* v_b_1912_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_eq(v_i_1910_, v_stop_1911_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; size_t v___x_1917_; size_t v___x_1918_; 
v___x_1915_ = lean_array_uget_borrowed(v_as_1909_, v_i_1910_);
lean_inc_ref(v___x_1906_);
v___x_1916_ = l_Lake_logToStream(v___x_1915_, v___x_1906_, v___x_1907_, v___x_1908_);
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_add(v_i_1910_, v___x_1917_);
v_i_1910_ = v___x_1918_;
v_b_1912_ = v___x_1916_;
goto _start;
}
else
{
lean_dec_ref(v___x_1906_);
return v_b_1912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_1920_, lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v_as_1923_, lean_object* v_i_1924_, lean_object* v_stop_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_){
_start:
{
uint8_t v___x_1083__boxed_1928_; uint8_t v___x_1084__boxed_1929_; size_t v_i_boxed_1930_; size_t v_stop_boxed_1931_; lean_object* v_res_1932_; 
v___x_1083__boxed_1928_ = lean_unbox(v___x_1921_);
v___x_1084__boxed_1929_ = lean_unbox(v___x_1922_);
v_i_boxed_1930_ = lean_unbox_usize(v_i_1924_);
lean_dec(v_i_1924_);
v_stop_boxed_1931_ = lean_unbox_usize(v_stop_1925_);
lean_dec(v_stop_1925_);
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1920_, v___x_1083__boxed_1928_, v___x_1084__boxed_1929_, v_as_1923_, v_i_boxed_1930_, v_stop_boxed_1931_, v_b_1926_);
lean_dec_ref(v_as_1923_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_1933_, uint8_t v___x_1934_, uint8_t v___x_1935_, lean_object* v_ws_1936_, lean_object* v_outputsRef_x3f_1937_, lean_object* v_out_1938_, lean_object* v_outputsFile_1939_, uint8_t v_isVerbose_1940_){
_start:
{
lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1958_; lean_object* v___y_1959_; uint8_t v___x_2045_; 
v___x_2045_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1936_);
if (v___x_2045_ == 0)
{
lean_object* v_packages_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_baseName_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_packages_2046_ = lean_ctor_get(v_ws_1936_, 4);
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = lean_array_fget_borrowed(v_packages_2046_, v___x_2047_);
v_baseName_2049_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_baseName_2049_);
v___x_2050_ = l_Lean_Name_toString(v_baseName_2049_, v___x_2045_);
v___x_2051_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15));
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
v___x_2053_ = 2;
v___x_2054_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*1, v___x_2053_);
lean_inc_ref(v___x_1933_);
v___x_2055_ = l_Lake_logToStream(v___x_2054_, v___x_1933_, v___x_1934_, v___x_1935_);
lean_dec_ref(v___x_2054_);
goto v___jp_1971_;
}
else
{
goto v___jp_1971_;
}
v___jp_1942_:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_box(0);
return v___x_1943_;
}
v___jp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = lean_array_get_size(v___y_1946_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_nat_dec_lt(v___y_1945_, v___x_1947_);
if (v___x_1949_ == 0)
{
lean_dec_ref(v___y_1946_);
lean_dec_ref(v___x_1933_);
return v___x_1948_;
}
else
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_nat_dec_le(v___x_1947_, v___x_1947_);
if (v___x_1950_ == 0)
{
if (v___x_1949_ == 0)
{
lean_dec_ref(v___y_1946_);
lean_dec_ref(v___x_1933_);
return v___x_1948_;
}
else
{
size_t v___x_1951_; size_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = ((size_t)0ULL);
v___x_1952_ = lean_usize_of_nat(v___x_1947_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1933_, v___x_1934_, v___x_1935_, v___y_1946_, v___x_1951_, v___x_1952_, v___x_1948_);
lean_dec_ref(v___y_1946_);
return v___x_1953_;
}
}
else
{
size_t v___x_1954_; size_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = lean_usize_of_nat(v___x_1947_);
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1933_, v___x_1934_, v___x_1935_, v___y_1946_, v___x_1954_, v___x_1955_, v___x_1948_);
lean_dec_ref(v___y_1946_);
return v___x_1956_;
}
}
}
v___jp_1957_:
{
if (v_isVerbose_1940_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v___y_1959_);
lean_dec_ref(v___x_1933_);
v___x_1960_ = lean_box(0);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1961_ = lean_array_get_size(v___y_1959_);
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_nat_dec_lt(v___y_1958_, v___x_1961_);
if (v___x_1963_ == 0)
{
lean_dec_ref(v___y_1959_);
lean_dec_ref(v___x_1933_);
return v___x_1962_;
}
else
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_nat_dec_le(v___x_1961_, v___x_1961_);
if (v___x_1964_ == 0)
{
if (v___x_1963_ == 0)
{
lean_dec_ref(v___y_1959_);
lean_dec_ref(v___x_1933_);
return v___x_1962_;
}
else
{
size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = lean_usize_of_nat(v___x_1961_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1933_, v___x_1934_, v___x_1935_, v___y_1959_, v___x_1965_, v___x_1966_, v___x_1962_);
lean_dec_ref(v___y_1959_);
return v___x_1967_;
}
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1961_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1933_, v___x_1934_, v___x_1935_, v___y_1959_, v___x_1968_, v___x_1969_, v___x_1962_);
lean_dec_ref(v___y_1959_);
return v___x_1970_;
}
}
}
}
v___jp_1971_:
{
if (lean_obj_tag(v_outputsRef_x3f_1937_) == 1)
{
lean_object* v_val_1972_; lean_object* v___x_1973_; lean_object* v_packages_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_config_1977_; lean_object* v_toLeanConfig_1978_; lean_object* v_platformIndependent_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_val_1972_ = lean_ctor_get(v_outputsRef_x3f_1937_, 0);
v___x_1973_ = lean_st_ref_get(v_val_1972_);
v_packages_1974_ = lean_ctor_get(v_ws_1936_, 4);
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_array_fget_borrowed(v_packages_1974_, v___x_1975_);
v_config_1977_ = lean_ctor_get(v___x_1976_, 6);
v_toLeanConfig_1978_ = lean_ctor_get(v_config_1977_, 1);
v_platformIndependent_1979_ = lean_ctor_get(v_toLeanConfig_1978_, 10);
v___x_1980_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1981_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_1979_, v___x_1980_);
v___x_1982_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_1983_ = l_Lake_CacheMap_writeFile(v_outputsFile_1939_, v___x_1973_, v___x_1981_, v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_a_1984_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = lean_array_get_size(v_a_1984_);
v___x_1986_ = lean_nat_dec_eq(v___x_1985_, v___x_1975_);
if (v___x_1986_ == 0)
{
if (v_isVerbose_1940_ == 0)
{
lean_dec(v_a_1984_);
lean_dec_ref(v_out_1938_);
lean_dec_ref(v___x_1933_);
goto v___jp_1942_;
}
else
{
lean_object* v_putStr_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_putStr_1987_ = lean_ctor_get(v_out_1938_, 4);
lean_inc_ref(v_putStr_1987_);
lean_dec_ref(v_out_1938_);
v___x_1988_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1989_ = lean_apply_2(v_putStr_1987_, v___x_1988_, lean_box(0));
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref(v___x_1989_);
v___y_1945_ = v___x_1975_;
v___y_1946_ = v_a_1984_;
goto v___jp_1944_;
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
v___x_1991_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1992_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1993_ = lean_unsigned_to_nat(89u);
v___x_1994_ = lean_unsigned_to_nat(4u);
v___x_1995_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1996_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1997_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1996_, v_isVerbose_1940_);
v___x_1998_ = lean_string_append(v___x_1995_, v___x_1997_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2000_ = lean_string_append(v___x_1998_, v___x_1999_);
v___x_2001_ = lean_io_error_to_string(v_a_1990_);
v___x_2002_ = lean_string_append(v___x_2000_, v___x_2001_);
lean_dec_ref(v___x_2001_);
v___x_2003_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2004_ = lean_string_append(v___x_2002_, v___x_2003_);
v___x_2005_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_2006_ = lean_string_append(v___x_2004_, v___x_2005_);
v___x_2007_ = l_mkPanicMessageWithDecl(v___x_1991_, v___x_1992_, v___x_1993_, v___x_1994_, v___x_2006_);
lean_dec_ref(v___x_2006_);
v___x_2008_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2007_);
v___y_1945_ = v___x_1975_;
v___y_1946_ = v_a_1984_;
goto v___jp_1944_;
}
}
}
else
{
lean_dec(v_a_1984_);
lean_dec_ref(v_out_1938_);
lean_dec_ref(v___x_1933_);
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v_putStr_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_a_2009_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_1983_);
v_putStr_2010_ = lean_ctor_get(v_out_1938_, 4);
lean_inc_ref(v_putStr_2010_);
lean_dec_ref(v_out_1938_);
v___x_2011_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7));
v___x_2012_ = lean_apply_2(v_putStr_2010_, v___x_2011_, lean_box(0));
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref(v___x_2012_);
v___y_1958_ = v___x_1975_;
v___y_1959_ = v_a_2009_;
goto v___jp_1957_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2015_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2016_ = lean_unsigned_to_nat(89u);
v___x_2017_ = lean_unsigned_to_nat(4u);
v___x_2018_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2019_ = lean_io_error_to_string(v_a_2013_);
v___x_2020_ = lean_string_append(v___x_2018_, v___x_2019_);
lean_dec_ref(v___x_2019_);
v___x_2021_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2022_ = lean_string_append(v___x_2020_, v___x_2021_);
v___x_2023_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_2024_ = lean_string_append(v___x_2022_, v___x_2023_);
v___x_2025_ = l_mkPanicMessageWithDecl(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2017_, v___x_2024_);
lean_dec_ref(v___x_2024_);
v___x_2026_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2025_);
v___y_1958_ = v___x_1975_;
v___y_1959_ = v_a_2009_;
goto v___jp_1957_;
}
}
}
else
{
lean_object* v_putStr_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v_outputsFile_1939_);
lean_dec_ref(v___x_1933_);
v_putStr_2027_ = lean_ctor_get(v_out_1938_, 4);
lean_inc_ref(v_putStr_2027_);
lean_dec_ref(v_out_1938_);
v___x_2028_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11));
v___x_2029_ = lean_apply_2(v_putStr_2027_, v___x_2028_, lean_box(0));
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
return v_a_2030_;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_a_2031_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2029_);
v___x_2032_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2033_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2034_ = lean_unsigned_to_nat(89u);
v___x_2035_ = lean_unsigned_to_nat(4u);
v___x_2036_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2037_ = lean_io_error_to_string(v_a_2031_);
v___x_2038_ = lean_string_append(v___x_2036_, v___x_2037_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2040_ = lean_string_append(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
v___x_2043_ = l_mkPanicMessageWithDecl(v___x_2032_, v___x_2033_, v___x_2034_, v___x_2035_, v___x_2042_);
lean_dec_ref(v___x_2042_);
v___x_2044_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2043_);
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2056_, lean_object* v___x_2057_, lean_object* v___x_2058_, lean_object* v_ws_2059_, lean_object* v_outputsRef_x3f_2060_, lean_object* v_out_2061_, lean_object* v_outputsFile_2062_, lean_object* v_isVerbose_2063_, lean_object* v_a_2064_){
_start:
{
uint8_t v___x_1253__boxed_2065_; uint8_t v___x_1254__boxed_2066_; uint8_t v_isVerbose_boxed_2067_; lean_object* v_res_2068_; 
v___x_1253__boxed_2065_ = lean_unbox(v___x_2057_);
v___x_1254__boxed_2066_ = lean_unbox(v___x_2058_);
v_isVerbose_boxed_2067_ = lean_unbox(v_isVerbose_2063_);
v_res_2068_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2056_, v___x_1253__boxed_2065_, v___x_1254__boxed_2066_, v_ws_2059_, v_outputsRef_x3f_2060_, v_out_2061_, v_outputsFile_2062_, v_isVerbose_boxed_2067_);
lean_dec(v_outputsRef_x3f_2060_);
lean_dec_ref(v_ws_2059_);
return v_res_2068_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = 3;
v___x_2070_ = lean_uint32_to_uint8(v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2071_, lean_object* v_bctx_2072_, lean_object* v_mctx_2073_, lean_object* v_result_2074_){
_start:
{
lean_object* v___y_2077_; lean_object* v_out_2080_; uint8_t v_outLv_2081_; uint8_t v_useAnsi_2082_; lean_object* v_toMonitorResult_2083_; lean_object* v_out_2084_; lean_object* v___x_2085_; uint8_t v_noBuild_2086_; uint8_t v_verbosity_2087_; lean_object* v_outputsFile_x3f_2088_; 
v_out_2080_ = lean_ctor_get(v_mctx_2073_, 1);
lean_inc_ref_n(v_out_2080_, 2);
v_outLv_2081_ = lean_ctor_get_uint8(v_mctx_2073_, sizeof(void*)*3);
v_useAnsi_2082_ = lean_ctor_get_uint8(v_mctx_2073_, sizeof(void*)*3 + 4);
lean_dec_ref(v_mctx_2073_);
v_toMonitorResult_2083_ = lean_ctor_get(v_result_2074_, 0);
lean_inc_ref_n(v_toMonitorResult_2083_, 2);
v_out_2084_ = lean_ctor_get(v_result_2074_, 1);
lean_inc_ref(v_out_2084_);
lean_dec_ref(v_result_2074_);
v___x_2085_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2071_, v_out_2080_, v_toMonitorResult_2083_);
v_noBuild_2086_ = lean_ctor_get_uint8(v_cfg_2071_, sizeof(void*)*3 + 2);
v_verbosity_2087_ = lean_ctor_get_uint8(v_cfg_2071_, sizeof(void*)*3 + 3);
v_outputsFile_x3f_2088_ = lean_ctor_get(v_cfg_2071_, 1);
lean_inc(v_outputsFile_x3f_2088_);
lean_dec_ref(v_cfg_2071_);
if (lean_obj_tag(v_outputsFile_x3f_2088_) == 1)
{
lean_object* v_val_2103_; lean_object* v_toContext_2104_; lean_object* v_outputsRef_x3f_2105_; uint8_t v___y_2107_; 
v_val_2103_ = lean_ctor_get(v_outputsFile_x3f_2088_, 0);
lean_inc(v_val_2103_);
lean_dec_ref(v_outputsFile_x3f_2088_);
v_toContext_2104_ = lean_ctor_get(v_bctx_2072_, 1);
v_outputsRef_x3f_2105_ = lean_ctor_get(v_bctx_2072_, 4);
if (v_verbosity_2087_ == 2)
{
uint8_t v___x_2109_; 
v___x_2109_ = 1;
v___y_2107_ = v___x_2109_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = 0;
v___y_2107_ = v___x_2110_;
goto v___jp_2106_;
}
v___jp_2106_:
{
lean_object* v___x_2108_; 
lean_inc_ref(v_out_2080_);
v___x_2108_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2080_, v_outLv_2081_, v_useAnsi_2082_, v_toContext_2104_, v_outputsRef_x3f_2105_, v_out_2080_, v_val_2103_, v___y_2107_);
goto v___jp_2089_;
}
}
else
{
lean_dec(v_outputsFile_x3f_2088_);
lean_dec_ref(v_out_2080_);
goto v___jp_2089_;
}
v___jp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_mk_io_user_error(v___y_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
v___jp_2089_:
{
if (lean_obj_tag(v_out_2084_) == 0)
{
if (v_noBuild_2086_ == 0)
{
lean_object* v_a_2090_; 
lean_dec_ref(v_toMonitorResult_2083_);
v_a_2090_ = lean_ctor_get(v_out_2084_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v_out_2084_);
v___y_2077_ = v_a_2090_;
goto v___jp_2076_;
}
else
{
uint8_t v_wantsRebuild_2091_; 
v_wantsRebuild_2091_ = lean_ctor_get_uint8(v_toMonitorResult_2083_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2083_);
if (v_wantsRebuild_2091_ == 0)
{
lean_object* v_a_2092_; 
v_a_2092_ = lean_ctor_get(v_out_2084_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v_out_2084_);
v___y_2077_ = v_a_2092_;
goto v___jp_2076_;
}
else
{
uint8_t v___x_2093_; lean_object* v___x_2094_; 
lean_dec_ref(v_out_2084_);
v___x_2093_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2094_ = lean_io_exit(v___x_2093_);
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_toMonitorResult_2083_);
v_a_2095_ = lean_ctor_get(v_out_2084_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_out_2084_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v_out_2084_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v_out_2084_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 0);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2111_, lean_object* v_bctx_2112_, lean_object* v_mctx_2113_, lean_object* v_result_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2111_, v_bctx_2112_, v_mctx_2113_, v_result_2114_);
lean_dec_ref(v_bctx_2112_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2117_, lean_object* v_cfg_2118_, lean_object* v_bctx_2119_, lean_object* v_mctx_2120_, lean_object* v_result_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2118_, v_bctx_2119_, v_mctx_2120_, v_result_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_cfg_2125_, lean_object* v_bctx_2126_, lean_object* v_mctx_2127_, lean_object* v_result_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2124_, v_cfg_2125_, v_bctx_2126_, v_mctx_2127_, v_result_2128_);
lean_dec_ref(v_bctx_2126_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2131_, lean_object* v_build_2132_, lean_object* v_cfg_2133_, lean_object* v_caption_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2136_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2137_ = lean_st_mk_ref(v___x_2136_);
lean_inc(v___x_2137_);
v___x_2138_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2133_, v___x_2137_);
lean_inc_ref(v_cfg_2133_);
v___x_2139_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2131_, v_cfg_2133_, v___x_2137_);
v___x_2140_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2139_, v_build_2132_, v_caption_2134_);
v___x_2141_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2138_, v___x_2140_);
v___x_2142_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2133_, v___x_2139_, v___x_2138_, v___x_2141_);
lean_dec_ref(v___x_2139_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2143_, lean_object* v_build_2144_, lean_object* v_cfg_2145_, lean_object* v_caption_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2143_, v_build_2144_, v_cfg_2145_, v_caption_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2149_, lean_object* v_ws_2150_, lean_object* v_build_2151_, lean_object* v_cfg_2152_, lean_object* v_caption_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2150_, v_build_2151_, v_cfg_2152_, v_caption_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2156_, lean_object* v_ws_2157_, lean_object* v_build_2158_, lean_object* v_cfg_2159_, lean_object* v_caption_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2156_, v_ws_2157_, v_build_2158_, v_cfg_2159_, v_caption_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2166_, lean_object* v_job_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v_out_2170_; 
v___x_2169_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2166_, v_job_2167_);
v_out_2170_ = lean_ctor_get(v___x_2169_, 1);
lean_inc_ref(v_out_2170_);
if (lean_obj_tag(v_out_2170_) == 0)
{
lean_object* v_toMonitorResult_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2186_; 
v_toMonitorResult_2171_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; 
v_unused_2187_ = lean_ctor_get(v___x_2169_, 1);
lean_dec(v_unused_2187_);
v___x_2173_ = v___x_2169_;
v_isShared_2174_ = v_isSharedCheck_2186_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_toMonitorResult_2171_);
lean_dec(v___x_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2186_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2185_; 
v_a_2175_ = lean_ctor_get(v_out_2170_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_out_2170_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2177_ = v_out_2170_;
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v_out_2170_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2180_);
v___x_2182_ = v___x_2173_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_toMonitorResult_2171_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2211_; 
v_a_2188_ = lean_ctor_get(v_out_2170_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_out_2170_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2190_ = v_out_2170_;
v_isShared_2191_ = v_isSharedCheck_2211_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v_out_2170_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2211_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v_toMonitorResult_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2209_; 
v_toMonitorResult_2192_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2169_, 1);
lean_dec(v_unused_2210_);
v___x_2194_ = v___x_2169_;
v_isShared_2195_ = v_isSharedCheck_2209_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_toMonitorResult_2192_);
lean_dec(v___x_2169_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2209_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_task_2196_; lean_object* v___x_2197_; 
v_task_2196_ = lean_ctor_get(v_a_2188_, 0);
lean_inc_ref(v_task_2196_);
lean_dec(v_a_2188_);
v___x_2197_ = lean_io_wait(v_task_2196_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v_a_2198_);
v___x_2200_ = v___x_2190_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2200_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2202_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2200_);
v___x_2202_ = v___x_2194_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_toMonitorResult_2192_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_dec_ref(v___x_2197_);
lean_del_object(v___x_2190_);
v___x_2205_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v___x_2205_);
v___x_2207_ = v___x_2194_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_toMonitorResult_2192_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2212_, lean_object* v_job_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2212_, v_job_2213_);
lean_dec_ref(v_mctx_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2216_, lean_object* v_mctx_2217_, lean_object* v_job_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2217_, v_job_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_mctx_2222_, lean_object* v_job_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2221_, v_mctx_2222_, v_job_2223_);
lean_dec_ref(v_mctx_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2239_, lean_object* v_build_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_out_2252_; 
v___x_2242_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2243_ = lean_st_mk_ref(v___x_2242_);
v___x_2244_ = 0;
v___x_2245_ = 1;
v___x_2246_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2243_);
v___x_2247_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2246_, v___x_2243_);
v___x_2248_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2239_, v___x_2246_, v___x_2243_);
v___x_2249_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2250_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2248_, v_build_2240_, v___x_2249_);
lean_dec_ref(v___x_2248_);
v___x_2251_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2247_, v___x_2250_);
lean_dec_ref(v___x_2247_);
v_out_2252_ = lean_ctor_get(v___x_2251_, 1);
lean_inc_ref(v_out_2252_);
lean_dec_ref(v___x_2251_);
if (lean_obj_tag(v_out_2252_) == 0)
{
lean_dec_ref(v_out_2252_);
return v___x_2244_;
}
else
{
lean_dec_ref(v_out_2252_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2253_, lean_object* v_build_2254_, lean_object* v_a_2255_){
_start:
{
uint8_t v_res_2256_; lean_object* v_r_2257_; 
v_res_2256_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2253_, v_build_2254_);
v_r_2257_ = lean_box(v_res_2256_);
return v_r_2257_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2258_, lean_object* v_ws_2259_, lean_object* v_build_2260_){
_start:
{
uint8_t v___x_2262_; 
v___x_2262_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2259_, v_build_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_ws_2264_, lean_object* v_build_2265_, lean_object* v_a_2266_){
_start:
{
uint8_t v_res_2267_; lean_object* v_r_2268_; 
v_res_2267_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2263_, v_ws_2264_, v_build_2265_);
v_r_2268_ = lean_box(v_res_2267_);
return v_r_2268_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2269_, lean_object* v_build_2270_, lean_object* v_cfg_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2273_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2274_ = lean_st_mk_ref(v___x_2273_);
lean_inc(v___x_2274_);
v___x_2275_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2271_, v___x_2274_);
lean_inc_ref(v_cfg_2271_);
v___x_2276_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2269_, v_cfg_2271_, v___x_2274_);
v___x_2277_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2278_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2276_, v_build_2270_, v___x_2277_);
v___x_2279_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2275_, v___x_2278_);
v___x_2280_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2271_, v___x_2276_, v___x_2275_, v___x_2279_);
lean_dec_ref(v___x_2276_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2281_, lean_object* v_build_2282_, lean_object* v_cfg_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lake_Workspace_runBuild___redArg(v_ws_2281_, v_build_2282_, v_cfg_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2286_, lean_object* v_ws_2287_, lean_object* v_build_2288_, lean_object* v_cfg_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lake_Workspace_runBuild___redArg(v_ws_2287_, v_build_2288_, v_cfg_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_ws_2293_, lean_object* v_build_2294_, lean_object* v_cfg_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lake_Workspace_runBuild(v_00_u03b1_2292_, v_ws_2293_, v_build_2294_, v_cfg_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2298_, lean_object* v_cfg_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; 
lean_inc(v_a_2300_);
v___x_2302_ = l_Lake_Workspace_runBuild___redArg(v_a_2300_, v_build_2298_, v_cfg_2299_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2303_, lean_object* v_cfg_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lake_runBuild___redArg(v_build_2303_, v_cfg_2304_, v_a_2305_);
lean_dec(v_a_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2308_, lean_object* v_build_2309_, lean_object* v_cfg_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___x_2313_; 
lean_inc(v_a_2311_);
v___x_2313_ = l_Lake_Workspace_runBuild___redArg(v_a_2311_, v_build_2309_, v_cfg_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2314_, lean_object* v_build_2315_, lean_object* v_cfg_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lake_runBuild(v_00_u03b1_2314_, v_build_2315_, v_cfg_2316_, v_a_2317_);
lean_dec(v_a_2317_);
return v_res_2319_;
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
