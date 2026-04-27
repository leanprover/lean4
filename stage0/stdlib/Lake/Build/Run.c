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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_mkBuildContext___closed__0_value),((lean_object*)&l_Lake_mkBuildContext___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_value;
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
lean_inc_n(v___x_879_, 2);
v___x_895_ = lean_array_push(v_fst_877_, v___x_879_);
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
lean_dec_ref(v___y_926_);
lean_dec_ref(v_as_922_);
return v_res_931_;
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
v___x_973_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0));
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
lean_dec_ref(v_a_988_);
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
lean_dec_ref(v_a_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v_snd_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1122_; 
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
v_flush_1088_ = lean_ctor_get(v_out_1087_, 0);
v_putStr_1089_ = lean_ctor_get(v_out_1087_, 4);
lean_inc_ref(v_putStr_1089_);
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
v___x_1099_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1100_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1101_ = lean_unsigned_to_nat(89u);
v___x_1102_ = lean_unsigned_to_nat(4u);
v___x_1103_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1104_ = lean_io_error_to_string(v_a_1095_);
v___x_1105_ = lean_string_append(v___x_1103_, v___x_1104_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
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
lean_inc_ref(v_flush_1088_);
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
lean_dec_ref(v_a_1125_);
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
v___x_1159_ = 3;
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
lean_dec_ref(v_ctx_1180_);
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
lean_dec_ref(v_ctx_1200_);
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___f_1236_; 
v___x_1235_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_1236_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1236_, 0, v___x_1235_);
return v___f_1236_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1244_ = l_String_quote(v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
v___x_1246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = l_Std_Format_defWidth;
v___x_1249_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5);
v___x_1250_ = l_Std_Format_pretty(v___x_1249_, v___x_1248_, v___x_1247_, v___x_1247_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7));
v___x_1253_ = l_String_quote(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
v___x_1255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = l_Std_Format_defWidth;
v___x_1258_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_1259_ = l_Std_Format_pretty(v___x_1258_, v___x_1257_, v___x_1256_, v___x_1256_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11));
v___x_1262_ = l_String_quote(v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
v___x_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = l_Std_Format_defWidth;
v___x_1267_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_1268_ = l_Std_Format_pretty(v___x_1267_, v___x_1266_, v___x_1265_, v___x_1265_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1270_, lean_object* v_ws_1271_, lean_object* v_outputsRef_x3f_1272_, lean_object* v_out_1273_, lean_object* v_outputsFile_1274_, uint8_t v_isVerbose_1275_){
_start:
{
lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1297_; lean_object* v___y_1298_; uint8_t v___x_1393_; 
lean_inc_ref(v_logger_1270_);
v___f_1279_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1279_, 0, v_logger_1270_);
v___x_1280_ = l_instMonadBaseIO;
v___x_1393_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1271_);
if (v___x_1393_ == 0)
{
lean_object* v_packages_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_baseName_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_packages_1394_ = lean_ctor_get(v_ws_1271_, 4);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_array_fget_borrowed(v_packages_1394_, v___x_1395_);
v_baseName_1397_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_baseName_1397_);
v___x_1398_ = l_Lean_Name_toString(v_baseName_1397_, v___x_1393_);
v___x_1399_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15));
v___x_1400_ = lean_string_append(v___x_1398_, v___x_1399_);
v___x_1401_ = 2;
v___x_1402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*1, v___x_1401_);
v___x_1403_ = lean_apply_2(v_logger_1270_, v___x_1402_, lean_box(0));
goto v___jp_1312_;
}
else
{
lean_dec_ref(v_logger_1270_);
goto v___jp_1312_;
}
v___jp_1277_:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_box(0);
return v___x_1278_;
}
v___jp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_array_get_size(v___y_1283_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_nat_dec_lt(v___y_1282_, v___x_1284_);
if (v___x_1286_ == 0)
{
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___f_1279_);
return v___x_1285_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_le(v___x_1284_, v___x_1284_);
if (v___x_1287_ == 0)
{
if (v___x_1286_ == 0)
{
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___f_1279_);
return v___x_1285_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1971__overap_1290_; lean_object* v___x_1291_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1284_);
v___x_1971__overap_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1280_, v___f_1279_, v___y_1283_, v___x_1288_, v___x_1289_, v___x_1285_);
v___x_1291_ = lean_apply_1(v___x_1971__overap_1290_, lean_box(0));
return v___x_1291_;
}
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1975__overap_1294_; lean_object* v___x_1295_; 
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1284_);
v___x_1975__overap_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1280_, v___f_1279_, v___y_1283_, v___x_1292_, v___x_1293_, v___x_1285_);
v___x_1295_ = lean_apply_1(v___x_1975__overap_1294_, lean_box(0));
return v___x_1295_;
}
}
}
v___jp_1296_:
{
if (v_isVerbose_1275_ == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___f_1279_);
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = lean_array_get_size(v___y_1297_);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_nat_dec_lt(v___y_1298_, v___x_1300_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___f_1279_);
return v___x_1301_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_nat_dec_le(v___x_1300_, v___x_1300_);
if (v___x_1303_ == 0)
{
if (v___x_1302_ == 0)
{
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___f_1279_);
return v___x_1301_;
}
else
{
size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1875__overap_1306_; lean_object* v___x_1307_; 
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = lean_usize_of_nat(v___x_1300_);
v___x_1875__overap_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1280_, v___f_1279_, v___y_1297_, v___x_1304_, v___x_1305_, v___x_1301_);
v___x_1307_ = lean_apply_1(v___x_1875__overap_1306_, lean_box(0));
return v___x_1307_;
}
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1879__overap_1310_; lean_object* v___x_1311_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1300_);
v___x_1879__overap_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1280_, v___f_1279_, v___y_1297_, v___x_1308_, v___x_1309_, v___x_1301_);
v___x_1311_ = lean_apply_1(v___x_1879__overap_1310_, lean_box(0));
return v___x_1311_;
}
}
}
}
v___jp_1312_:
{
if (lean_obj_tag(v_outputsRef_x3f_1272_) == 1)
{
lean_object* v_val_1313_; lean_object* v___x_1314_; lean_object* v_packages_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_config_1318_; lean_object* v_toLeanConfig_1319_; lean_object* v_platformIndependent_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_val_1313_ = lean_ctor_get(v_outputsRef_x3f_1272_, 0);
v___x_1314_ = lean_st_ref_get(v_val_1313_);
v_packages_1315_ = lean_ctor_get(v_ws_1271_, 4);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_array_fget_borrowed(v_packages_1315_, v___x_1316_);
v_config_1318_ = lean_ctor_get(v___x_1317_, 6);
v_toLeanConfig_1319_ = lean_ctor_get(v_config_1318_, 1);
v_platformIndependent_1320_ = lean_ctor_get(v_toLeanConfig_1319_, 10);
v___f_1321_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0);
v___x_1322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
lean_inc(v_platformIndependent_1320_);
v___x_1323_ = l_Option_instBEq_beq___redArg(v___f_1321_, v_platformIndependent_1320_, v___x_1322_);
v___x_1324_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_1325_ = l_Lake_CacheMap_writeFile(v_outputsFile_1274_, v___x_1314_, v___x_1323_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = lean_array_get_size(v_a_1326_);
v___x_1328_ = lean_nat_dec_eq(v___x_1327_, v___x_1316_);
if (v___x_1328_ == 0)
{
if (v_isVerbose_1275_ == 0)
{
lean_dec(v_a_1326_);
lean_dec_ref(v___f_1279_);
lean_dec_ref(v_out_1273_);
goto v___jp_1277_;
}
else
{
lean_object* v_putStr_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_putStr_1329_ = lean_ctor_get(v_out_1273_, 4);
lean_inc_ref(v_putStr_1329_);
lean_dec_ref(v_out_1273_);
v___x_1330_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1331_ = lean_apply_2(v_putStr_1329_, v___x_1330_, lean_box(0));
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_dec_ref(v___x_1331_);
v___y_1282_ = v___x_1316_;
v___y_1283_ = v_a_1326_;
goto v___jp_1281_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_2113__overap_1351_; lean_object* v___x_1352_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1334_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1335_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1336_ = lean_unsigned_to_nat(89u);
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1339_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1340_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1339_, v_isVerbose_1275_);
v___x_1341_ = lean_string_append(v___x_1338_, v___x_1340_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1343_ = lean_string_append(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_io_error_to_string(v_a_1332_);
v___x_1345_ = lean_string_append(v___x_1343_, v___x_1344_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1347_ = lean_string_append(v___x_1345_, v___x_1346_);
v___x_1348_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1349_ = lean_string_append(v___x_1347_, v___x_1348_);
v___x_1350_ = l_mkPanicMessageWithDecl(v___x_1334_, v___x_1335_, v___x_1336_, v___x_1337_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_2113__overap_1351_ = l_panic___redArg(v___x_1333_, v___x_1350_);
v___x_1352_ = lean_apply_1(v___x_2113__overap_1351_, lean_box(0));
v___y_1282_ = v___x_1316_;
v___y_1283_ = v_a_1326_;
goto v___jp_1281_;
}
}
}
else
{
lean_dec(v_a_1326_);
lean_dec_ref(v___f_1279_);
lean_dec_ref(v_out_1273_);
goto v___jp_1277_;
}
}
else
{
lean_object* v_a_1353_; lean_object* v_putStr_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_a_1353_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1325_);
v_putStr_1354_ = lean_ctor_get(v_out_1273_, 4);
lean_inc_ref(v_putStr_1354_);
lean_dec_ref(v_out_1273_);
v___x_1355_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7));
v___x_1356_ = lean_apply_2(v_putStr_1354_, v___x_1355_, lean_box(0));
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref(v___x_1356_);
v___y_1297_ = v_a_1353_;
v___y_1298_ = v___x_1316_;
goto v___jp_1296_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1770__overap_1371_; lean_object* v___x_1372_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1359_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1360_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1361_ = lean_unsigned_to_nat(89u);
v___x_1362_ = lean_unsigned_to_nat(4u);
v___x_1363_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1364_ = lean_io_error_to_string(v_a_1357_);
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
lean_dec_ref(v___x_1364_);
v___x_1366_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
v___x_1368_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1369_ = lean_string_append(v___x_1367_, v___x_1368_);
v___x_1370_ = l_mkPanicMessageWithDecl(v___x_1359_, v___x_1360_, v___x_1361_, v___x_1362_, v___x_1369_);
lean_dec_ref(v___x_1369_);
v___x_1770__overap_1371_ = l_panic___redArg(v___x_1358_, v___x_1370_);
v___x_1372_ = lean_apply_1(v___x_1770__overap_1371_, lean_box(0));
v___y_1297_ = v_a_1353_;
v___y_1298_ = v___x_1316_;
goto v___jp_1296_;
}
}
}
else
{
lean_object* v_putStr_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v___f_1279_);
lean_dec_ref(v_outputsFile_1274_);
v_putStr_1373_ = lean_ctor_get(v_out_1273_, 4);
lean_inc_ref(v_putStr_1373_);
lean_dec_ref(v_out_1273_);
v___x_1374_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11));
v___x_1375_ = lean_apply_2(v_putStr_1373_, v___x_1374_, lean_box(0));
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
return v_a_1376_;
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1925__overap_1391_; lean_object* v___x_1392_; 
v_a_1377_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1375_);
v___x_1378_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1379_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1380_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1381_ = lean_unsigned_to_nat(89u);
v___x_1382_ = lean_unsigned_to_nat(4u);
v___x_1383_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1384_ = lean_io_error_to_string(v_a_1377_);
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
v___x_1388_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
v___x_1390_ = l_mkPanicMessageWithDecl(v___x_1379_, v___x_1380_, v___x_1381_, v___x_1382_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1925__overap_1391_ = l_panic___redArg(v___x_1378_, v___x_1390_);
v___x_1392_ = lean_apply_1(v___x_1925__overap_1391_, lean_box(0));
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1404_, lean_object* v_ws_1405_, lean_object* v_outputsRef_x3f_1406_, lean_object* v_out_1407_, lean_object* v_outputsFile_1408_, lean_object* v_isVerbose_1409_, lean_object* v_a_1410_){
_start:
{
uint8_t v_isVerbose_boxed_1411_; lean_object* v_res_1412_; 
v_isVerbose_boxed_1411_ = lean_unbox(v_isVerbose_1409_);
v_res_1412_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1404_, v_ws_1405_, v_outputsRef_x3f_1406_, v_out_1407_, v_outputsFile_1408_, v_isVerbose_boxed_1411_);
lean_dec(v_outputsRef_x3f_1406_);
lean_dec_ref(v_ws_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1414_, lean_object* v_as_1415_, size_t v_i_1416_, size_t v_stop_1417_, lean_object* v_b_1418_){
_start:
{
lean_object* v_val_1421_; uint8_t v___x_1425_; 
v___x_1425_ = lean_usize_dec_eq(v_i_1416_, v_stop_1417_);
if (v___x_1425_ == 0)
{
lean_object* v_putStr_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_putStr_1426_ = lean_ctor_get(v_out_1414_, 4);
v___x_1427_ = lean_array_uget_borrowed(v_as_1415_, v_i_1416_);
v___x_1428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1429_ = lean_string_append(v___x_1428_, v___x_1427_);
v___x_1430_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1431_ = lean_string_append(v___x_1429_, v___x_1430_);
lean_inc_ref(v_putStr_1426_);
lean_inc_ref(v___x_1431_);
v___x_1432_ = lean_apply_2(v_putStr_1426_, v___x_1431_, lean_box(0));
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; 
lean_dec_ref(v___x_1431_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
v_val_1421_ = v_a_1433_;
goto v___jp_1420_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1457_; 
v_a_1434_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1436_ = v___x_1432_;
v_isShared_1437_ = v_isSharedCheck_1457_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1457_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1438_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1439_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1440_ = lean_unsigned_to_nat(89u);
v___x_1441_ = lean_unsigned_to_nat(4u);
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1444_ = lean_io_error_to_string(v_a_1434_);
v___x_1445_ = lean_string_append(v___x_1443_, v___x_1444_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1447_ = lean_string_append(v___x_1445_, v___x_1446_);
v___x_1448_ = l_String_quote(v___x_1431_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 3);
lean_ctor_set(v___x_1436_, 0, v___x_1448_);
v___x_1450_ = v___x_1436_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1451_ = l_Std_Format_defWidth;
v___x_1452_ = l_Std_Format_pretty(v___x_1450_, v___x_1451_, v___x_1442_, v___x_1442_);
v___x_1453_ = lean_string_append(v___x_1447_, v___x_1452_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1438_, v___x_1439_, v___x_1440_, v___x_1441_, v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1454_);
v_val_1421_ = v___x_1455_;
goto v___jp_1420_;
}
}
}
}
else
{
lean_dec_ref(v_out_1414_);
return v_b_1418_;
}
v___jp_1420_:
{
size_t v___x_1422_; size_t v___x_1423_; 
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1416_, v___x_1422_);
v_i_1416_ = v___x_1423_;
v_b_1418_ = v_val_1421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1458_, lean_object* v_as_1459_, lean_object* v_i_1460_, lean_object* v_stop_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_){
_start:
{
size_t v_i_boxed_1464_; size_t v_stop_boxed_1465_; lean_object* v_res_1466_; 
v_i_boxed_1464_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_stop_boxed_1465_ = lean_unbox_usize(v_stop_1461_);
lean_dec(v_stop_1461_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1458_, v_as_1459_, v_i_boxed_1464_, v_stop_boxed_1465_, v_b_1462_);
lean_dec_ref(v_as_1459_);
return v_res_1466_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1474_ = l_String_quote(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = l_Std_Format_defWidth;
v___x_1479_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1480_ = l_Std_Format_pretty(v___x_1479_, v___x_1478_, v___x_1477_, v___x_1477_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1481_, lean_object* v_out_1482_, lean_object* v_result_1483_){
_start:
{
uint8_t v___y_1486_; lean_object* v___y_1487_; lean_object* v_failures_1561_; lean_object* v_numJobs_1562_; uint8_t v___y_1564_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_failures_1561_ = lean_ctor_get(v_result_1483_, 0);
lean_inc_ref(v_failures_1561_);
v_numJobs_1562_ = lean_ctor_get(v_result_1483_, 1);
lean_inc(v_numJobs_1562_);
lean_dec_ref(v_result_1483_);
v___x_1572_ = lean_array_get_size(v_failures_1561_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_nat_dec_eq(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v_flush_1575_; lean_object* v_putStr_1576_; lean_object* v___y_1582_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_numJobs_1562_);
v_flush_1575_ = lean_ctor_get(v_out_1482_, 0);
lean_inc_ref(v_flush_1575_);
v_putStr_1576_ = lean_ctor_get(v_out_1482_, 4);
v___x_1593_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
lean_inc_ref(v_putStr_1576_);
v___x_1594_ = lean_apply_2(v_putStr_1576_, v___x_1593_, lean_box(0));
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_dec_ref(v___x_1594_);
goto v___jp_1583_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1597_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1598_ = lean_unsigned_to_nat(89u);
v___x_1599_ = lean_unsigned_to_nat(4u);
v___x_1600_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1601_ = lean_io_error_to_string(v_a_1595_);
v___x_1602_ = lean_string_append(v___x_1600_, v___x_1601_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
v___x_1605_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
v___x_1607_ = l_mkPanicMessageWithDecl(v___x_1596_, v___x_1597_, v___x_1598_, v___x_1599_, v___x_1606_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1607_);
goto v___jp_1583_;
}
v___jp_1577_:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_apply_1(v_flush_1575_, lean_box(0));
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
return v_a_1579_;
}
else
{
lean_object* v___x_1580_; 
lean_dec_ref(v___x_1578_);
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
}
v___jp_1581_:
{
goto v___jp_1577_;
}
v___jp_1583_:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_nat_dec_lt(v___x_1573_, v___x_1572_);
if (v___x_1584_ == 0)
{
lean_dec_ref(v_failures_1561_);
lean_dec_ref(v_out_1482_);
goto v___jp_1577_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_nat_dec_le(v___x_1572_, v___x_1572_);
if (v___x_1586_ == 0)
{
if (v___x_1584_ == 0)
{
lean_dec_ref(v_failures_1561_);
lean_dec_ref(v_out_1482_);
goto v___jp_1577_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = lean_usize_of_nat(v___x_1572_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1482_, v_failures_1561_, v___x_1587_, v___x_1588_, v___x_1585_);
lean_dec_ref(v_failures_1561_);
v___y_1582_ = v___x_1589_;
goto v___jp_1581_;
}
}
else
{
size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = lean_usize_of_nat(v___x_1572_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1482_, v_failures_1561_, v___x_1590_, v___x_1591_, v___x_1585_);
lean_dec_ref(v_failures_1561_);
v___y_1582_ = v___x_1592_;
goto v___jp_1581_;
}
}
}
}
else
{
uint8_t v___x_1609_; 
lean_dec_ref(v_failures_1561_);
v___x_1609_ = l_Lake_BuildConfig_showProgress(v_cfg_1481_);
if (v___x_1609_ == 0)
{
v___y_1564_ = v___x_1609_;
goto v___jp_1563_;
}
else
{
uint8_t v_showSuccess_1610_; 
v_showSuccess_1610_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*2 + 4);
v___y_1564_ = v_showSuccess_1610_;
goto v___jp_1563_;
}
}
v___jp_1485_:
{
uint8_t v_noBuild_1488_; 
v_noBuild_1488_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*2 + 2);
if (v_noBuild_1488_ == 0)
{
lean_object* v_putStr_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_putStr_1489_ = lean_ctor_get(v_out_1482_, 4);
lean_inc_ref(v_putStr_1489_);
lean_dec_ref(v_out_1482_);
v___x_1490_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1491_ = lean_string_append(v___x_1490_, v___y_1487_);
lean_dec_ref(v___y_1487_);
v___x_1492_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1493_ = lean_string_append(v___x_1491_, v___x_1492_);
lean_inc_ref(v___x_1493_);
v___x_1494_ = lean_apply_2(v_putStr_1489_, v___x_1493_, lean_box(0));
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; 
lean_dec_ref(v___x_1493_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
return v_a_1495_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1524_; 
v_a_1496_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1498_ = v___x_1494_;
v_isShared_1499_ = v_isSharedCheck_1524_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1524_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1500_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1501_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1502_ = lean_unsigned_to_nat(89u);
v___x_1503_ = lean_unsigned_to_nat(4u);
v___x_1504_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1507_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1506_, v___y_1486_);
v___x_1508_ = lean_string_append(v___x_1504_, v___x_1507_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1510_ = lean_string_append(v___x_1508_, v___x_1509_);
v___x_1511_ = lean_io_error_to_string(v_a_1496_);
v___x_1512_ = lean_string_append(v___x_1510_, v___x_1511_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1514_ = lean_string_append(v___x_1512_, v___x_1513_);
v___x_1515_ = l_String_quote(v___x_1493_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 3);
lean_ctor_set(v___x_1498_, 0, v___x_1515_);
v___x_1517_ = v___x_1498_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1518_ = l_Std_Format_defWidth;
v___x_1519_ = l_Std_Format_pretty(v___x_1517_, v___x_1518_, v___x_1505_, v___x_1505_);
v___x_1520_ = lean_string_append(v___x_1514_, v___x_1519_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = l_mkPanicMessageWithDecl(v___x_1500_, v___x_1501_, v___x_1502_, v___x_1503_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1521_);
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_putStr_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_putStr_1525_ = lean_ctor_get(v_out_1482_, 4);
lean_inc_ref(v_putStr_1525_);
lean_dec_ref(v_out_1482_);
v___x_1526_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1527_ = lean_string_append(v___x_1526_, v___y_1487_);
lean_dec_ref(v___y_1487_);
v___x_1528_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
lean_inc_ref(v___x_1529_);
v___x_1530_ = lean_apply_2(v_putStr_1525_, v___x_1529_, lean_box(0));
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; 
lean_dec_ref(v___x_1529_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref(v___x_1530_);
return v_a_1531_;
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1560_; 
v_a_1532_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1534_ = v___x_1530_;
v_isShared_1535_ = v_isSharedCheck_1560_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1530_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1560_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1536_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1537_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1538_ = lean_unsigned_to_nat(89u);
v___x_1539_ = lean_unsigned_to_nat(4u);
v___x_1540_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1542_, v_noBuild_1488_);
v___x_1544_ = lean_string_append(v___x_1540_, v___x_1543_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1546_ = lean_string_append(v___x_1544_, v___x_1545_);
v___x_1547_ = lean_io_error_to_string(v_a_1532_);
v___x_1548_ = lean_string_append(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1550_ = lean_string_append(v___x_1548_, v___x_1549_);
v___x_1551_ = l_String_quote(v___x_1529_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 3);
lean_ctor_set(v___x_1534_, 0, v___x_1551_);
v___x_1553_ = v___x_1534_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1554_ = l_Std_Format_defWidth;
v___x_1555_ = l_Std_Format_pretty(v___x_1553_, v___x_1554_, v___x_1541_, v___x_1541_);
v___x_1556_ = lean_string_append(v___x_1550_, v___x_1555_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = l_mkPanicMessageWithDecl(v___x_1536_, v___x_1537_, v___x_1538_, v___x_1539_, v___x_1556_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1557_);
return v___x_1558_;
}
}
}
}
}
v___jp_1563_:
{
if (v___y_1564_ == 0)
{
lean_object* v___x_1565_; 
lean_dec(v_numJobs_1562_);
lean_dec_ref(v_out_1482_);
v___x_1565_ = lean_box(0);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_nat_dec_eq(v_numJobs_1562_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = l_Nat_reprFast(v_numJobs_1562_);
v___x_1569_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1570_ = lean_string_append(v___x_1568_, v___x_1569_);
v___y_1486_ = v___y_1564_;
v___y_1487_ = v___x_1570_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1571_; 
lean_dec(v_numJobs_1562_);
v___x_1571_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1486_ = v___y_1564_;
v___y_1487_ = v___x_1571_;
goto v___jp_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1611_, lean_object* v_out_1612_, lean_object* v_result_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1611_, v_out_1612_, v_result_1613_);
lean_dec_ref(v_cfg_1611_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1616_){
_start:
{
lean_object* v_toMonitorResult_1617_; 
v_toMonitorResult_1617_ = lean_ctor_get(v_self_1616_, 0);
lean_inc_ref(v_toMonitorResult_1617_);
return v_toMonitorResult_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1618_);
lean_dec_ref(v_self_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1621_){
_start:
{
lean_object* v___f_1622_; 
v___f_1622_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1622_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1623_){
_start:
{
lean_object* v_out_1624_; 
v_out_1624_ = lean_ctor_get(v_self_1623_, 1);
if (lean_obj_tag(v_out_1624_) == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = 0;
return v___x_1625_;
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = 1;
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1627_);
lean_dec_ref(v_self_1627_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1630_, lean_object* v_self_1631_){
_start:
{
lean_object* v_out_1632_; 
v_out_1632_ = lean_ctor_get(v_self_1631_, 1);
if (lean_obj_tag(v_out_1632_) == 0)
{
uint8_t v___x_1633_; 
v___x_1633_ = 0;
return v___x_1633_;
}
else
{
uint8_t v___x_1634_; 
v___x_1634_ = 1;
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1635_, lean_object* v_self_1636_){
_start:
{
uint8_t v_res_1637_; lean_object* v_r_1638_; 
v_res_1637_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1635_, v_self_1636_);
lean_dec_ref(v_self_1636_);
v_r_1638_ = lean_box(v_res_1637_);
return v_r_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1647_, lean_object* v_job_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v_failures_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_inc_ref(v_job_1648_);
v___x_1650_ = l_Lake_Job_toOpaque___redArg(v_job_1648_);
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_mk_empty_array_with_capacity(v___x_1651_);
v___x_1653_ = lean_array_push(v___x_1652_, v___x_1650_);
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1656_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1657_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1647_, v___x_1653_, v___x_1655_, v___x_1656_);
v_failures_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc_ref(v_failures_1658_);
v___x_1659_ = lean_array_get_size(v_failures_1658_);
lean_dec_ref(v_failures_1658_);
v___x_1660_ = lean_nat_dec_eq(v___x_1659_, v___x_1654_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec_ref(v_job_1648_);
v___x_1661_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1657_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
return v___x_1662_;
}
else
{
lean_object* v_task_1663_; lean_object* v___x_1664_; 
v_task_1663_ = lean_ctor_get(v_job_1648_, 0);
lean_inc_ref(v_task_1663_);
lean_dec_ref(v_job_1648_);
v___x_1664_ = lean_io_wait(v_task_1663_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1664_, 1);
lean_dec(v_unused_1674_);
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_a_1665_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1669_);
lean_ctor_set(v___x_1667_, 0, v___x_1657_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1682_; 
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; 
v_unused_1683_ = lean_ctor_get(v___x_1664_, 1);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v___x_1664_, 0);
lean_dec(v_unused_1684_);
v___x_1676_ = v___x_1664_;
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v___x_1664_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 0);
lean_ctor_set(v___x_1676_, 1, v___x_1678_);
lean_ctor_set(v___x_1676_, 0, v___x_1657_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1685_, lean_object* v_job_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1685_, v_job_1686_);
lean_dec_ref(v_ctx_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1689_, lean_object* v_ctx_1690_, lean_object* v_job_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1690_, v_job_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_ctx_1695_, lean_object* v_job_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1694_, v_ctx_1695_, v_job_1696_);
lean_dec_ref(v_ctx_1695_);
return v_res_1698_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_unsigned_to_nat(16u);
v___x_1703_ = lean_mk_array(v___x_1702_, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1);
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___x_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* v_ws_1707_, lean_object* v_cfg_1708_, lean_object* v_jobs_1709_){
_start:
{
lean_object* v_val_1712_; lean_object* v_outputsFile_x3f_1724_; 
v_outputsFile_x3f_1724_ = lean_ctor_get(v_cfg_1708_, 1);
lean_inc(v_outputsFile_x3f_1724_);
if (lean_obj_tag(v_outputsFile_x3f_1724_) == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_box(0);
v_val_1712_ = v___x_1725_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
v_isSharedCheck_1734_ = !lean_is_exclusive(v_outputsFile_x3f_1724_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_outputsFile_x3f_1724_, 0);
lean_dec(v_unused_1735_);
v___x_1727_ = v_outputsFile_x3f_1724_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v_outputsFile_x3f_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1729_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2);
v___x_1730_ = lean_st_mk_ref(v___x_1729_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1730_);
v___x_1732_ = v___x_1727_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
v_val_1712_ = v___x_1732_;
goto v___jp_1711_;
}
}
}
v___jp_1711_:
{
lean_object* v_lakeEnv_1713_; lean_object* v___x_1714_; uint64_t v___x_1715_; uint64_t v___x_1716_; uint64_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_lakeEnv_1713_ = lean_ctor_get(v_ws_1707_, 0);
v___x_1714_ = l_Lake_Env_leanGithash(v_lakeEnv_1713_);
v___x_1715_ = l_Lake_Hash_nil;
v___x_1716_ = lean_string_hash(v___x_1714_);
v___x_1717_ = lean_uint64_mix_hash(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_1719_ = lean_string_append(v___x_1718_, v___x_1714_);
lean_dec_ref(v___x_1714_);
v___x_1720_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
v___x_1721_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_1722_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1722_, 0, v___x_1719_);
lean_ctor_set(v___x_1722_, 1, v___x_1720_);
lean_ctor_set(v___x_1722_, 2, v___x_1721_);
lean_ctor_set_uint64(v___x_1722_, sizeof(void*)*3, v___x_1717_);
v___x_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1723_, 0, v_cfg_1708_);
lean_ctor_set(v___x_1723_, 1, v_ws_1707_);
lean_ctor_set(v___x_1723_, 2, v___x_1722_);
lean_ctor_set(v___x_1723_, 3, v_jobs_1709_);
lean_ctor_set(v___x_1723_, 4, v_val_1712_);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(lean_object* v_ws_1736_, lean_object* v_cfg_1737_, lean_object* v_jobs_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_1736_, v_cfg_1737_, v_jobs_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_log_1749_; uint8_t v_action_1750_; uint8_t v_wantsRebuild_1751_; lean_object* v_trace_1752_; lean_object* v_buildTime_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1782_; 
v_log_1749_ = lean_ctor_get(v___y_1747_, 0);
v_action_1750_ = lean_ctor_get_uint8(v___y_1747_, sizeof(void*)*3);
v_wantsRebuild_1751_ = lean_ctor_get_uint8(v___y_1747_, sizeof(void*)*3 + 1);
v_trace_1752_ = lean_ctor_get(v___y_1747_, 1);
v_buildTime_1753_ = lean_ctor_get(v___y_1747_, 2);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___y_1747_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1755_ = v___y_1747_;
v_isShared_1756_ = v_isSharedCheck_1782_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_buildTime_1753_);
lean_inc(v_trace_1752_);
lean_inc(v_log_1749_);
lean_dec(v___y_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1782_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_apply_7(v_build_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v_log_1749_, lean_box(0));
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_a_1759_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1761_ = v___x_1757_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_a_1759_);
v___x_1764_ = v___x_1755_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1759_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_trace_1752_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_buildTime_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*3, v_action_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*3 + 1, v_wantsRebuild_1751_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1758_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1781_; 
v_a_1770_ = lean_ctor_get(v___x_1757_, 0);
v_a_1771_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1773_ = v___x_1757_;
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_inc(v_a_1770_);
lean_dec(v___x_1757_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_a_1771_);
v___x_1776_ = v___x_1755_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1771_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_trace_1752_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_buildTime_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1780_, sizeof(void*)*3, v_action_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1780_, sizeof(void*)*3 + 1, v_wantsRebuild_1751_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1770_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_1793_, lean_object* v_build_1794_, lean_object* v_caption_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1797_ = lean_box(1);
v___x_1798_ = lean_st_mk_ref(v___x_1797_);
v___f_1799_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1799_, 0, v_build_1794_);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_box(0);
v___x_1804_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_1805_ = l_Lake_Job_async___redArg(v___x_1800_, v___f_1799_, v___x_1801_, v_caption_1795_, v___x_1804_, v___x_1803_, v___x_1802_, v___x_1798_, v_bctx_1793_);
v___x_1806_ = lean_st_ref_get(v___x_1798_);
lean_dec(v___x_1798_);
lean_dec(v___x_1806_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_1807_, lean_object* v_build_1808_, lean_object* v_caption_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1807_, v_build_1808_, v_caption_1809_);
lean_dec_ref(v_bctx_1807_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_1812_, lean_object* v_bctx_1813_, lean_object* v_build_1814_, lean_object* v_caption_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1813_, v_build_1814_, v_caption_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_bctx_1819_, lean_object* v_build_1820_, lean_object* v_caption_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_1818_, v_bctx_1819_, v_build_1820_, v_caption_1821_);
lean_dec_ref(v_bctx_1819_);
return v_res_1823_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
if (lean_obj_tag(v_x_1824_) == 0)
{
if (lean_obj_tag(v_x_1825_) == 0)
{
uint8_t v___x_1826_; 
v___x_1826_ = 1;
return v___x_1826_;
}
else
{
uint8_t v___x_1827_; 
v___x_1827_ = 0;
return v___x_1827_;
}
}
else
{
if (lean_obj_tag(v_x_1825_) == 0)
{
uint8_t v___x_1828_; 
v___x_1828_ = 0;
return v___x_1828_;
}
else
{
lean_object* v_val_1829_; uint8_t v___x_1830_; 
v_val_1829_ = lean_ctor_get(v_x_1824_, 0);
v___x_1830_ = lean_unbox(v_val_1829_);
if (v___x_1830_ == 0)
{
lean_object* v_val_1831_; uint8_t v___x_1832_; 
v_val_1831_ = lean_ctor_get(v_x_1825_, 0);
v___x_1832_ = lean_unbox(v_val_1831_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
v___x_1833_ = 1;
return v___x_1833_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_unbox(v_val_1829_);
return v___x_1834_;
}
}
else
{
lean_object* v_val_1835_; uint8_t v___x_1836_; 
v_val_1835_ = lean_ctor_get(v_x_1825_, 0);
v___x_1836_ = lean_unbox(v_val_1835_);
return v___x_1836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
uint8_t v_res_1839_; lean_object* v_r_1840_; 
v_res_1839_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_1837_, v_x_1838_);
lean_dec(v_x_1838_);
lean_dec(v_x_1837_);
v_r_1840_ = lean_box(v_res_1839_);
return v_r_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_1841_, uint8_t v___x_1842_, uint8_t v___x_1843_, lean_object* v_as_1844_, size_t v_i_1845_, size_t v_stop_1846_, lean_object* v_b_1847_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_usize_dec_eq(v_i_1845_, v_stop_1846_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; 
v___x_1850_ = lean_array_uget_borrowed(v_as_1844_, v_i_1845_);
lean_inc_ref(v___x_1841_);
v___x_1851_ = l_Lake_logToStream(v___x_1850_, v___x_1841_, v___x_1842_, v___x_1843_);
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = lean_usize_add(v_i_1845_, v___x_1852_);
v_i_1845_ = v___x_1853_;
v_b_1847_ = v___x_1851_;
goto _start;
}
else
{
lean_dec_ref(v___x_1841_);
return v_b_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_1855_, lean_object* v___x_1856_, lean_object* v___x_1857_, lean_object* v_as_1858_, lean_object* v_i_1859_, lean_object* v_stop_1860_, lean_object* v_b_1861_, lean_object* v___y_1862_){
_start:
{
uint8_t v___x_1083__boxed_1863_; uint8_t v___x_1084__boxed_1864_; size_t v_i_boxed_1865_; size_t v_stop_boxed_1866_; lean_object* v_res_1867_; 
v___x_1083__boxed_1863_ = lean_unbox(v___x_1856_);
v___x_1084__boxed_1864_ = lean_unbox(v___x_1857_);
v_i_boxed_1865_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_stop_boxed_1866_ = lean_unbox_usize(v_stop_1860_);
lean_dec(v_stop_1860_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1855_, v___x_1083__boxed_1863_, v___x_1084__boxed_1864_, v_as_1858_, v_i_boxed_1865_, v_stop_boxed_1866_, v_b_1861_);
lean_dec_ref(v_as_1858_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_1868_, uint8_t v___x_1869_, uint8_t v___x_1870_, lean_object* v_ws_1871_, lean_object* v_outputsRef_x3f_1872_, lean_object* v_out_1873_, lean_object* v_outputsFile_1874_, uint8_t v_isVerbose_1875_){
_start:
{
lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1893_; lean_object* v___y_1894_; uint8_t v___x_1980_; 
v___x_1980_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1871_);
if (v___x_1980_ == 0)
{
lean_object* v_packages_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_baseName_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_packages_1981_ = lean_ctor_get(v_ws_1871_, 4);
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_array_fget_borrowed(v_packages_1981_, v___x_1982_);
v_baseName_1984_ = lean_ctor_get(v___x_1983_, 1);
lean_inc(v_baseName_1984_);
v___x_1985_ = l_Lean_Name_toString(v_baseName_1984_, v___x_1980_);
v___x_1986_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15));
v___x_1987_ = lean_string_append(v___x_1985_, v___x_1986_);
v___x_1988_ = 2;
v___x_1989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*1, v___x_1988_);
lean_inc_ref(v___x_1868_);
v___x_1990_ = l_Lake_logToStream(v___x_1989_, v___x_1868_, v___x_1869_, v___x_1870_);
lean_dec_ref(v___x_1989_);
goto v___jp_1906_;
}
else
{
goto v___jp_1906_;
}
v___jp_1877_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_box(0);
return v___x_1878_;
}
v___jp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1882_ = lean_array_get_size(v___y_1881_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_nat_dec_lt(v___y_1880_, v___x_1882_);
if (v___x_1884_ == 0)
{
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___x_1868_);
return v___x_1883_;
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_nat_dec_le(v___x_1882_, v___x_1882_);
if (v___x_1885_ == 0)
{
if (v___x_1884_ == 0)
{
lean_dec_ref(v___y_1881_);
lean_dec_ref(v___x_1868_);
return v___x_1883_;
}
else
{
size_t v___x_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = lean_usize_of_nat(v___x_1882_);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1868_, v___x_1869_, v___x_1870_, v___y_1881_, v___x_1886_, v___x_1887_, v___x_1883_);
lean_dec_ref(v___y_1881_);
return v___x_1888_;
}
}
else
{
size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___x_1882_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1868_, v___x_1869_, v___x_1870_, v___y_1881_, v___x_1889_, v___x_1890_, v___x_1883_);
lean_dec_ref(v___y_1881_);
return v___x_1891_;
}
}
}
v___jp_1892_:
{
if (v_isVerbose_1875_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___x_1868_);
v___x_1895_ = lean_box(0);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = lean_array_get_size(v___y_1894_);
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_nat_dec_lt(v___y_1893_, v___x_1896_);
if (v___x_1898_ == 0)
{
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___x_1868_);
return v___x_1897_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_nat_dec_le(v___x_1896_, v___x_1896_);
if (v___x_1899_ == 0)
{
if (v___x_1898_ == 0)
{
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___x_1868_);
return v___x_1897_;
}
else
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = lean_usize_of_nat(v___x_1896_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1868_, v___x_1869_, v___x_1870_, v___y_1894_, v___x_1900_, v___x_1901_, v___x_1897_);
lean_dec_ref(v___y_1894_);
return v___x_1902_;
}
}
else
{
size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = lean_usize_of_nat(v___x_1896_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1868_, v___x_1869_, v___x_1870_, v___y_1894_, v___x_1903_, v___x_1904_, v___x_1897_);
lean_dec_ref(v___y_1894_);
return v___x_1905_;
}
}
}
}
v___jp_1906_:
{
if (lean_obj_tag(v_outputsRef_x3f_1872_) == 1)
{
lean_object* v_val_1907_; lean_object* v___x_1908_; lean_object* v_packages_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_config_1912_; lean_object* v_toLeanConfig_1913_; lean_object* v_platformIndependent_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_val_1907_ = lean_ctor_get(v_outputsRef_x3f_1872_, 0);
v___x_1908_ = lean_st_ref_get(v_val_1907_);
v_packages_1909_ = lean_ctor_get(v_ws_1871_, 4);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_array_fget_borrowed(v_packages_1909_, v___x_1910_);
v_config_1912_ = lean_ctor_get(v___x_1911_, 6);
v_toLeanConfig_1913_ = lean_ctor_get(v_config_1912_, 1);
v_platformIndependent_1914_ = lean_ctor_get(v_toLeanConfig_1913_, 10);
v___x_1915_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1916_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_1914_, v___x_1915_);
v___x_1917_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_1918_ = l_Lake_CacheMap_writeFile(v_outputsFile_1874_, v___x_1908_, v___x_1916_, v___x_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 1);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = lean_array_get_size(v_a_1919_);
v___x_1921_ = lean_nat_dec_eq(v___x_1920_, v___x_1910_);
if (v___x_1921_ == 0)
{
if (v_isVerbose_1875_ == 0)
{
lean_dec(v_a_1919_);
lean_dec_ref(v_out_1873_);
lean_dec_ref(v___x_1868_);
goto v___jp_1877_;
}
else
{
lean_object* v_putStr_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_putStr_1922_ = lean_ctor_get(v_out_1873_, 4);
lean_inc_ref(v_putStr_1922_);
lean_dec_ref(v_out_1873_);
v___x_1923_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1924_ = lean_apply_2(v_putStr_1922_, v___x_1923_, lean_box(0));
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_dec_ref(v___x_1924_);
v___y_1880_ = v___x_1910_;
v___y_1881_ = v_a_1919_;
goto v___jp_1879_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1927_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1928_ = lean_unsigned_to_nat(89u);
v___x_1929_ = lean_unsigned_to_nat(4u);
v___x_1930_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1931_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1931_, v_isVerbose_1875_);
v___x_1933_ = lean_string_append(v___x_1930_, v___x_1932_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1935_ = lean_string_append(v___x_1933_, v___x_1934_);
v___x_1936_ = lean_io_error_to_string(v_a_1925_);
v___x_1937_ = lean_string_append(v___x_1935_, v___x_1936_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1939_ = lean_string_append(v___x_1937_, v___x_1938_);
v___x_1940_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1941_ = lean_string_append(v___x_1939_, v___x_1940_);
v___x_1942_ = l_mkPanicMessageWithDecl(v___x_1926_, v___x_1927_, v___x_1928_, v___x_1929_, v___x_1941_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1942_);
v___y_1880_ = v___x_1910_;
v___y_1881_ = v_a_1919_;
goto v___jp_1879_;
}
}
}
else
{
lean_dec(v_a_1919_);
lean_dec_ref(v_out_1873_);
lean_dec_ref(v___x_1868_);
goto v___jp_1877_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v_putStr_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_a_1944_ = lean_ctor_get(v___x_1918_, 1);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1918_);
v_putStr_1945_ = lean_ctor_get(v_out_1873_, 4);
lean_inc_ref(v_putStr_1945_);
lean_dec_ref(v_out_1873_);
v___x_1946_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7));
v___x_1947_ = lean_apply_2(v_putStr_1945_, v___x_1946_, lean_box(0));
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_dec_ref(v___x_1947_);
v___y_1893_ = v___x_1910_;
v___y_1894_ = v_a_1944_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1950_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1951_ = lean_unsigned_to_nat(89u);
v___x_1952_ = lean_unsigned_to_nat(4u);
v___x_1953_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1954_ = lean_io_error_to_string(v_a_1948_);
v___x_1955_ = lean_string_append(v___x_1953_, v___x_1954_);
lean_dec_ref(v___x_1954_);
v___x_1956_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1957_ = lean_string_append(v___x_1955_, v___x_1956_);
v___x_1958_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1959_ = lean_string_append(v___x_1957_, v___x_1958_);
v___x_1960_ = l_mkPanicMessageWithDecl(v___x_1949_, v___x_1950_, v___x_1951_, v___x_1952_, v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1960_);
v___y_1893_ = v___x_1910_;
v___y_1894_ = v_a_1944_;
goto v___jp_1892_;
}
}
}
else
{
lean_object* v_putStr_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v_outputsFile_1874_);
lean_dec_ref(v___x_1868_);
v_putStr_1962_ = lean_ctor_get(v_out_1873_, 4);
lean_inc_ref(v_putStr_1962_);
lean_dec_ref(v_out_1873_);
v___x_1963_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11));
v___x_1964_ = lean_apply_2(v_putStr_1962_, v___x_1963_, lean_box(0));
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
return v_a_1965_;
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1966_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1964_);
v___x_1967_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1968_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1969_ = lean_unsigned_to_nat(89u);
v___x_1970_ = lean_unsigned_to_nat(4u);
v___x_1971_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1972_ = lean_io_error_to_string(v_a_1966_);
v___x_1973_ = lean_string_append(v___x_1971_, v___x_1972_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1975_ = lean_string_append(v___x_1973_, v___x_1974_);
v___x_1976_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_1977_ = lean_string_append(v___x_1975_, v___x_1976_);
v___x_1978_ = l_mkPanicMessageWithDecl(v___x_1967_, v___x_1968_, v___x_1969_, v___x_1970_, v___x_1977_);
lean_dec_ref(v___x_1977_);
v___x_1979_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1978_);
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_1991_, lean_object* v___x_1992_, lean_object* v___x_1993_, lean_object* v_ws_1994_, lean_object* v_outputsRef_x3f_1995_, lean_object* v_out_1996_, lean_object* v_outputsFile_1997_, lean_object* v_isVerbose_1998_, lean_object* v_a_1999_){
_start:
{
uint8_t v___x_1253__boxed_2000_; uint8_t v___x_1254__boxed_2001_; uint8_t v_isVerbose_boxed_2002_; lean_object* v_res_2003_; 
v___x_1253__boxed_2000_ = lean_unbox(v___x_1992_);
v___x_1254__boxed_2001_ = lean_unbox(v___x_1993_);
v_isVerbose_boxed_2002_ = lean_unbox(v_isVerbose_1998_);
v_res_2003_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_1991_, v___x_1253__boxed_2000_, v___x_1254__boxed_2001_, v_ws_1994_, v_outputsRef_x3f_1995_, v_out_1996_, v_outputsFile_1997_, v_isVerbose_boxed_2002_);
lean_dec(v_outputsRef_x3f_1995_);
lean_dec_ref(v_ws_1994_);
return v_res_2003_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = 3;
v___x_2005_ = lean_uint32_to_uint8(v___x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2006_, lean_object* v_bctx_2007_, lean_object* v_mctx_2008_, lean_object* v_result_2009_){
_start:
{
lean_object* v___y_2012_; lean_object* v_out_2015_; uint8_t v_outLv_2016_; uint8_t v_useAnsi_2017_; lean_object* v_toMonitorResult_2018_; lean_object* v_out_2019_; lean_object* v___x_2020_; uint8_t v_noBuild_2021_; uint8_t v_verbosity_2022_; lean_object* v_outputsFile_x3f_2023_; 
v_out_2015_ = lean_ctor_get(v_mctx_2008_, 1);
lean_inc_ref_n(v_out_2015_, 2);
v_outLv_2016_ = lean_ctor_get_uint8(v_mctx_2008_, sizeof(void*)*3);
v_useAnsi_2017_ = lean_ctor_get_uint8(v_mctx_2008_, sizeof(void*)*3 + 4);
lean_dec_ref(v_mctx_2008_);
v_toMonitorResult_2018_ = lean_ctor_get(v_result_2009_, 0);
lean_inc_ref_n(v_toMonitorResult_2018_, 2);
v_out_2019_ = lean_ctor_get(v_result_2009_, 1);
lean_inc_ref(v_out_2019_);
lean_dec_ref(v_result_2009_);
v___x_2020_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2006_, v_out_2015_, v_toMonitorResult_2018_);
v_noBuild_2021_ = lean_ctor_get_uint8(v_cfg_2006_, sizeof(void*)*2 + 2);
v_verbosity_2022_ = lean_ctor_get_uint8(v_cfg_2006_, sizeof(void*)*2 + 3);
v_outputsFile_x3f_2023_ = lean_ctor_get(v_cfg_2006_, 1);
lean_inc(v_outputsFile_x3f_2023_);
lean_dec_ref(v_cfg_2006_);
if (lean_obj_tag(v_outputsFile_x3f_2023_) == 1)
{
lean_object* v_val_2038_; lean_object* v_toContext_2039_; lean_object* v_outputsRef_x3f_2040_; uint8_t v___y_2042_; 
v_val_2038_ = lean_ctor_get(v_outputsFile_x3f_2023_, 0);
lean_inc(v_val_2038_);
lean_dec_ref(v_outputsFile_x3f_2023_);
v_toContext_2039_ = lean_ctor_get(v_bctx_2007_, 1);
v_outputsRef_x3f_2040_ = lean_ctor_get(v_bctx_2007_, 4);
if (v_verbosity_2022_ == 2)
{
uint8_t v___x_2044_; 
v___x_2044_ = 1;
v___y_2042_ = v___x_2044_;
goto v___jp_2041_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = 0;
v___y_2042_ = v___x_2045_;
goto v___jp_2041_;
}
v___jp_2041_:
{
lean_object* v___x_2043_; 
lean_inc_ref(v_out_2015_);
v___x_2043_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2015_, v_outLv_2016_, v_useAnsi_2017_, v_toContext_2039_, v_outputsRef_x3f_2040_, v_out_2015_, v_val_2038_, v___y_2042_);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_outputsFile_x3f_2023_);
lean_dec_ref(v_out_2015_);
goto v___jp_2024_;
}
v___jp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_mk_io_user_error(v___y_2012_);
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
v___jp_2024_:
{
if (lean_obj_tag(v_out_2019_) == 0)
{
if (v_noBuild_2021_ == 0)
{
lean_object* v_a_2025_; 
lean_dec_ref(v_toMonitorResult_2018_);
v_a_2025_ = lean_ctor_get(v_out_2019_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v_out_2019_);
v___y_2012_ = v_a_2025_;
goto v___jp_2011_;
}
else
{
uint8_t v_wantsRebuild_2026_; 
v_wantsRebuild_2026_ = lean_ctor_get_uint8(v_toMonitorResult_2018_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2018_);
if (v_wantsRebuild_2026_ == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v_out_2019_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v_out_2019_);
v___y_2012_ = v_a_2027_;
goto v___jp_2011_;
}
else
{
uint8_t v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v_out_2019_);
v___x_2028_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2029_ = lean_io_exit(v___x_2028_);
return v___x_2029_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_toMonitorResult_2018_);
v_a_2030_ = lean_ctor_get(v_out_2019_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_out_2019_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v_out_2019_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v_out_2019_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 0);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2046_, lean_object* v_bctx_2047_, lean_object* v_mctx_2048_, lean_object* v_result_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2046_, v_bctx_2047_, v_mctx_2048_, v_result_2049_);
lean_dec_ref(v_bctx_2047_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2052_, lean_object* v_cfg_2053_, lean_object* v_bctx_2054_, lean_object* v_mctx_2055_, lean_object* v_result_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2053_, v_bctx_2054_, v_mctx_2055_, v_result_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2059_, lean_object* v_cfg_2060_, lean_object* v_bctx_2061_, lean_object* v_mctx_2062_, lean_object* v_result_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2059_, v_cfg_2060_, v_bctx_2061_, v_mctx_2062_, v_result_2063_);
lean_dec_ref(v_bctx_2061_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2066_, lean_object* v_build_2067_, lean_object* v_cfg_2068_, lean_object* v_caption_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2071_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2072_ = lean_st_mk_ref(v___x_2071_);
lean_inc(v___x_2072_);
v___x_2073_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2068_, v___x_2072_);
lean_inc_ref(v_cfg_2068_);
v___x_2074_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2066_, v_cfg_2068_, v___x_2072_);
v___x_2075_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2074_, v_build_2067_, v_caption_2069_);
v___x_2076_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2073_, v___x_2075_);
v___x_2077_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2068_, v___x_2074_, v___x_2073_, v___x_2076_);
lean_dec_ref(v___x_2074_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2078_, lean_object* v_build_2079_, lean_object* v_cfg_2080_, lean_object* v_caption_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2078_, v_build_2079_, v_cfg_2080_, v_caption_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2084_, lean_object* v_ws_2085_, lean_object* v_build_2086_, lean_object* v_cfg_2087_, lean_object* v_caption_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2085_, v_build_2086_, v_cfg_2087_, v_caption_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2091_, lean_object* v_ws_2092_, lean_object* v_build_2093_, lean_object* v_cfg_2094_, lean_object* v_caption_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2091_, v_ws_2092_, v_build_2093_, v_cfg_2094_, v_caption_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2101_, lean_object* v_job_2102_){
_start:
{
lean_object* v___x_2104_; lean_object* v_out_2105_; 
v___x_2104_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2101_, v_job_2102_);
v_out_2105_ = lean_ctor_get(v___x_2104_, 1);
lean_inc_ref(v_out_2105_);
if (lean_obj_tag(v_out_2105_) == 0)
{
lean_object* v_toMonitorResult_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2121_; 
v_toMonitorResult_2106_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v___x_2104_, 1);
lean_dec(v_unused_2122_);
v___x_2108_ = v___x_2104_;
v_isShared_2109_ = v_isSharedCheck_2121_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_toMonitorResult_2106_);
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2121_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2120_; 
v_a_2110_ = lean_ctor_get(v_out_2105_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_out_2105_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2112_ = v_out_2105_;
v_isShared_2113_ = v_isSharedCheck_2120_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v_out_2105_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2120_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v___x_2115_);
v___x_2117_ = v___x_2108_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_toMonitorResult_2106_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2146_; 
v_a_2123_ = lean_ctor_get(v_out_2105_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_out_2105_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2125_ = v_out_2105_;
v_isShared_2126_ = v_isSharedCheck_2146_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v_out_2105_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2146_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_toMonitorResult_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2144_; 
v_toMonitorResult_2127_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___x_2104_, 1);
lean_dec(v_unused_2145_);
v___x_2129_ = v___x_2104_;
v_isShared_2130_ = v_isSharedCheck_2144_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_toMonitorResult_2127_);
lean_dec(v___x_2104_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2144_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_task_2131_; lean_object* v___x_2132_; 
v_task_2131_ = lean_ctor_get(v_a_2123_, 0);
lean_inc_ref(v_task_2131_);
lean_dec(v_a_2123_);
v___x_2132_ = lean_io_wait(v_task_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v_a_2133_);
v___x_2135_ = v___x_2125_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___x_2135_);
v___x_2137_ = v___x_2129_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_toMonitorResult_2127_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
lean_dec_ref(v___x_2132_);
lean_del_object(v___x_2125_);
v___x_2140_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___x_2140_);
v___x_2142_ = v___x_2129_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_toMonitorResult_2127_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2147_, lean_object* v_job_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2147_, v_job_2148_);
lean_dec_ref(v_mctx_2147_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2151_, lean_object* v_mctx_2152_, lean_object* v_job_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2152_, v_job_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2156_, lean_object* v_mctx_2157_, lean_object* v_job_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2156_, v_mctx_2157_, v_job_2158_);
lean_dec_ref(v_mctx_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2173_, lean_object* v_build_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_out_2186_; 
v___x_2176_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2177_ = lean_st_mk_ref(v___x_2176_);
v___x_2178_ = 0;
v___x_2179_ = 1;
v___x_2180_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2177_);
v___x_2181_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2180_, v___x_2177_);
v___x_2182_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2173_, v___x_2180_, v___x_2177_);
v___x_2183_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2184_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2182_, v_build_2174_, v___x_2183_);
lean_dec_ref(v___x_2182_);
v___x_2185_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2181_, v___x_2184_);
lean_dec_ref(v___x_2181_);
v_out_2186_ = lean_ctor_get(v___x_2185_, 1);
lean_inc_ref(v_out_2186_);
lean_dec_ref(v___x_2185_);
if (lean_obj_tag(v_out_2186_) == 0)
{
lean_dec_ref(v_out_2186_);
return v___x_2178_;
}
else
{
lean_dec_ref(v_out_2186_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2187_, lean_object* v_build_2188_, lean_object* v_a_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2187_, v_build_2188_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2192_, lean_object* v_ws_2193_, lean_object* v_build_2194_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2193_, v_build_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_ws_2198_, lean_object* v_build_2199_, lean_object* v_a_2200_){
_start:
{
uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_res_2201_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2197_, v_ws_2198_, v_build_2199_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2203_, lean_object* v_build_2204_, lean_object* v_cfg_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2207_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2208_ = lean_st_mk_ref(v___x_2207_);
lean_inc(v___x_2208_);
v___x_2209_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2205_, v___x_2208_);
lean_inc_ref(v_cfg_2205_);
v___x_2210_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2203_, v_cfg_2205_, v___x_2208_);
v___x_2211_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2212_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2210_, v_build_2204_, v___x_2211_);
v___x_2213_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2209_, v___x_2212_);
v___x_2214_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2205_, v___x_2210_, v___x_2209_, v___x_2213_);
lean_dec_ref(v___x_2210_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2215_, lean_object* v_build_2216_, lean_object* v_cfg_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lake_Workspace_runBuild___redArg(v_ws_2215_, v_build_2216_, v_cfg_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2220_, lean_object* v_ws_2221_, lean_object* v_build_2222_, lean_object* v_cfg_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lake_Workspace_runBuild___redArg(v_ws_2221_, v_build_2222_, v_cfg_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_ws_2227_, lean_object* v_build_2228_, lean_object* v_cfg_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lake_Workspace_runBuild(v_00_u03b1_2226_, v_ws_2227_, v_build_2228_, v_cfg_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2232_, lean_object* v_cfg_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___x_2236_; 
lean_inc(v_a_2234_);
v___x_2236_ = l_Lake_Workspace_runBuild___redArg(v_a_2234_, v_build_2232_, v_cfg_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2237_, lean_object* v_cfg_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lake_runBuild___redArg(v_build_2237_, v_cfg_2238_, v_a_2239_);
lean_dec(v_a_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2242_, lean_object* v_build_2243_, lean_object* v_cfg_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; 
lean_inc(v_a_2245_);
v___x_2247_ = l_Lake_Workspace_runBuild___redArg(v_a_2245_, v_build_2243_, v_cfg_2244_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_build_2249_, lean_object* v_cfg_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lake_runBuild(v_00_u03b1_2248_, v_build_2249_, v_cfg_2250_, v_a_2251_);
lean_dec(v_a_2251_);
return v_res_2253_;
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
