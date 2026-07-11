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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_value;
static const lean_array_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = ": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_value;
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
lean_dec_ref_known(v___x_119_, 1);
return v_a_120_;
}
else
{
lean_object* v___x_121_; 
lean_dec_ref_known(v___x_119_, 1);
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
lean_dec_ref_known(v___x_172_, 1);
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
lean_dec_ref_known(v___x_213_, 1);
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
lean_dec_ref_known(v___x_254_, 1);
v_val_250_ = v_a_255_;
goto v___jp_249_;
}
else
{
lean_object* v___x_256_; 
lean_dec_ref_known(v___x_254_, 1);
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
lean_dec_ref_known(v___x_311_, 1);
v_val_307_ = v_a_312_;
goto v___jp_306_;
}
else
{
lean_object* v___x_313_; 
lean_dec_ref_known(v___x_311_, 1);
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
lean_dec_ref_known(v___x_332_, 1);
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
uint8_t v___y_16263__boxed_458_; uint8_t v_useAnsi_16264__boxed_459_; size_t v_i_boxed_460_; size_t v_stop_boxed_461_; lean_object* v_res_462_; 
v___y_16263__boxed_458_ = lean_unbox(v___y_450_);
v_useAnsi_16264__boxed_459_ = lean_unbox(v_useAnsi_451_);
v_i_boxed_460_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_449_, v___y_16263__boxed_458_, v_useAnsi_16264__boxed_459_, v_as_452_, v_i_boxed_460_, v_stop_boxed_461_, v_b_455_, v___y_456_);
lean_dec_ref(v_as_452_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___y_475_; lean_object* v_val_476_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_491_; lean_object* v_jobNo_494_; lean_object* v_totalJobs_495_; uint8_t v_wantsRebuild_496_; lean_object* v_failures_497_; lean_object* v_resetCtrl_498_; lean_object* v_lastUpdate_499_; lean_object* v_spinnerIdx_500_; lean_object* v_out_501_; uint8_t v_outLv_502_; uint8_t v_failLv_503_; uint8_t v_minAction_504_; uint8_t v_showOptional_505_; uint8_t v_useAnsi_506_; uint8_t v_showProgress_507_; uint8_t v_showTime_508_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; uint8_t v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; uint8_t v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; uint8_t v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; lean_object* v___y_606_; uint8_t v___y_607_; lean_object* v___y_608_; lean_object* v_task_610_; lean_object* v_caption_611_; uint8_t v_optional_612_; lean_object* v___y_614_; uint8_t v___y_615_; uint8_t v___y_616_; uint8_t v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; uint32_t v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; uint8_t v___y_625_; lean_object* v___y_626_; lean_object* v___y_649_; uint8_t v___y_650_; uint8_t v___y_651_; uint8_t v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; uint32_t v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_663_; uint8_t v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; uint8_t v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint32_t v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; uint8_t v___y_683_; uint8_t v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; uint8_t v___y_693_; uint32_t v___y_694_; uint8_t v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; uint8_t v___y_707_; uint8_t v___y_708_; uint8_t v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; uint8_t v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; uint8_t v___y_722_; uint8_t v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; uint8_t v___y_736_; uint8_t v___y_737_; uint8_t v___y_740_; uint8_t v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; uint8_t v___y_745_; uint8_t v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; uint8_t v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; uint8_t v___y_757_; uint8_t v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; uint8_t v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; uint8_t v___y_792_; uint8_t v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; uint8_t v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; uint8_t v___y_816_; uint8_t v___y_821_; lean_object* v___y_822_; uint8_t v___y_823_; uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; uint8_t v___y_835_; lean_object* v___y_836_; uint8_t v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; uint8_t v___y_842_; lean_object* v___y_847_; lean_object* v___x_858_; lean_object* v_a_859_; 
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
v___x_858_ = lean_task_get_own(v_task_610_);
v_a_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___y_847_ = v_a_859_;
goto v___jp_846_;
v___jp_474_:
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_val_476_);
lean_ctor_set(v___x_477_, 1, v___y_475_);
return v___x_477_;
}
v___jp_478_:
{
lean_object* v_out_481_; lean_object* v_flush_482_; lean_object* v___x_483_; 
v_out_481_ = lean_ctor_get(v___y_479_, 1);
v_flush_482_ = lean_ctor_get(v_out_481_, 0);
lean_inc_ref(v_flush_482_);
v___x_483_ = lean_apply_1(v_flush_482_, lean_box(0));
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___y_475_ = v___y_480_;
v_val_476_ = v_a_484_;
goto v___jp_474_;
}
else
{
lean_object* v___x_485_; 
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = lean_box(0);
v___y_475_ = v___y_480_;
v_val_476_ = v___x_485_;
goto v___jp_474_;
}
}
v___jp_486_:
{
lean_object* v_snd_489_; 
v_snd_489_ = lean_ctor_get(v___y_488_, 1);
lean_inc(v_snd_489_);
lean_dec_ref(v___y_488_);
v___y_479_ = v___y_487_;
v___y_480_ = v_snd_489_;
goto v___jp_478_;
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___y_491_);
return v___x_493_;
}
v___jp_509_:
{
uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_lt(v___y_511_, v___y_514_);
lean_dec(v___y_511_);
if (v___x_516_ == 0)
{
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
v___y_479_ = v___y_512_;
v___y_480_ = v___y_510_;
goto v___jp_478_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_nat_dec_le(v___y_514_, v___y_514_);
if (v___x_518_ == 0)
{
if (v___x_516_ == 0)
{
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
v___y_479_ = v___y_512_;
v___y_480_ = v___y_510_;
goto v___jp_478_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___y_514_);
lean_dec(v___y_514_);
lean_inc_ref(v_out_501_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_501_, v___y_515_, v_useAnsi_506_, v___y_513_, v___x_519_, v___x_520_, v___x_517_, v___y_510_);
lean_dec_ref(v___y_513_);
v___y_487_ = v___y_512_;
v___y_488_ = v___x_521_;
goto v___jp_486_;
}
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___y_514_);
lean_dec(v___y_514_);
lean_inc_ref(v_out_501_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_501_, v___y_515_, v_useAnsi_506_, v___y_513_, v___x_522_, v___x_523_, v___x_517_, v___y_510_);
lean_dec_ref(v___y_513_);
v___y_487_ = v___y_512_;
v___y_488_ = v___x_524_;
goto v___jp_486_;
}
}
}
v___jp_525_:
{
if (v___y_532_ == 0)
{
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_528_);
v___y_479_ = v___y_529_;
v___y_480_ = v___y_527_;
goto v___jp_478_;
}
else
{
if (v___y_526_ == 0)
{
v___y_510_ = v___y_527_;
v___y_511_ = v___y_528_;
v___y_512_ = v___y_529_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_531_;
v___y_515_ = v_outLv_502_;
goto v___jp_509_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = 0;
v___y_510_ = v___y_527_;
v___y_511_ = v___y_528_;
v___y_512_ = v___y_529_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_531_;
v___y_515_ = v___x_533_;
goto v___jp_509_;
}
}
}
v___jp_534_:
{
lean_object* v_out_544_; lean_object* v_jobNo_545_; lean_object* v_totalJobs_546_; uint8_t v_wantsRebuild_547_; lean_object* v_failures_548_; lean_object* v_resetCtrl_549_; lean_object* v_lastUpdate_550_; lean_object* v_spinnerIdx_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_597_; 
v_out_544_ = lean_ctor_get(v___y_537_, 1);
v_jobNo_545_ = lean_ctor_get(v___y_538_, 0);
v_totalJobs_546_ = lean_ctor_get(v___y_538_, 1);
v_wantsRebuild_547_ = lean_ctor_get_uint8(v___y_538_, sizeof(void*)*6);
v_failures_548_ = lean_ctor_get(v___y_538_, 2);
v_resetCtrl_549_ = lean_ctor_get(v___y_538_, 3);
v_lastUpdate_550_ = lean_ctor_get(v___y_538_, 4);
v_spinnerIdx_551_ = lean_ctor_get(v___y_538_, 5);
v_isSharedCheck_597_ = !lean_is_exclusive(v___y_538_);
if (v_isSharedCheck_597_ == 0)
{
v___x_553_ = v___y_538_;
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
lean_dec(v___y_538_);
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
lean_dec_ref_known(v___x_562_, 1);
lean_dec_ref(v___x_561_);
v___y_526_ = v___y_535_;
v___y_527_ = v___x_558_;
v___y_528_ = v___y_536_;
v___y_529_ = v___y_537_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
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
lean_inc(v___y_536_);
v___x_574_ = l_Lean_Name_num___override(v___x_573_, v___y_536_);
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
lean_inc_n(v___y_536_, 2);
v___x_590_ = l_Std_Format_pretty(v___x_588_, v___x_589_, v___y_536_, v___y_536_);
v___x_591_ = lean_string_append(v___x_585_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = l_mkPanicMessageWithDecl(v___x_567_, v___x_568_, v___x_569_, v___x_570_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_592_);
v___y_526_ = v___y_535_;
v___y_527_ = v___x_558_;
v___y_528_ = v___y_536_;
v___y_529_ = v___y_537_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
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
v___x_609_ = l_Lake_Ansi_chalk(v___y_608_, v___y_601_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_608_);
v___y_535_ = v___y_599_;
v___y_536_ = v___y_600_;
v___y_537_ = v___y_603_;
v___y_538_ = v___y_602_;
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
v___x_628_ = lean_string_push(v___x_627_, v___y_620_);
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
v___x_639_ = lean_string_append(v___x_638_, v___y_624_);
v___x_640_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
v___x_642_ = lean_string_append(v___x_641_, v___y_623_);
lean_dec_ref(v___y_623_);
v___x_643_ = lean_string_append(v___x_642_, v___x_640_);
v___x_644_ = lean_string_append(v___x_643_, v_caption_611_);
lean_dec_ref(v_caption_611_);
v___x_645_ = lean_string_append(v___x_644_, v___y_626_);
lean_dec_ref(v___y_626_);
if (v_useAnsi_506_ == 0)
{
v___y_535_ = v___y_616_;
v___y_536_ = v___y_618_;
v___y_537_ = v___y_619_;
v___y_538_ = v___y_614_;
v___y_539_ = v___y_615_;
v___y_540_ = v___y_621_;
v___y_541_ = v___y_622_;
v___y_542_ = v___y_625_;
v___y_543_ = v___x_645_;
goto v___jp_534_;
}
else
{
if (v___y_625_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_599_ = v___y_616_;
v___y_600_ = v___y_618_;
v___y_601_ = v___x_645_;
v___y_602_ = v___y_614_;
v___y_603_ = v___y_619_;
v___y_604_ = v___y_621_;
v___y_605_ = v___y_615_;
v___y_606_ = v___y_622_;
v___y_607_ = v___y_625_;
v___y_608_ = v___x_646_;
goto v___jp_598_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_Lake_LogLevel_ansiColor(v___y_617_);
v___y_599_ = v___y_616_;
v___y_600_ = v___y_618_;
v___y_601_ = v___x_645_;
v___y_602_ = v___y_614_;
v___y_603_ = v___y_619_;
v___y_604_ = v___y_621_;
v___y_605_ = v___y_615_;
v___y_606_ = v___y_622_;
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
lean_dec(v___y_665_);
v___y_649_ = v___y_663_;
v___y_650_ = v___y_664_;
v___y_651_ = v___y_666_;
v___y_652_ = v___y_667_;
v___y_653_ = v___y_668_;
v___y_654_ = v___y_669_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_672_;
v___y_658_ = v___y_673_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_674_;
goto v___jp_648_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_lt(v___y_668_, v___y_665_);
if (v___x_676_ == 0)
{
lean_dec(v___y_665_);
v___y_649_ = v___y_663_;
v___y_650_ = v___y_664_;
v___y_651_ = v___y_666_;
v___y_652_ = v___y_667_;
v___y_653_ = v___y_668_;
v___y_654_ = v___y_669_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_672_;
v___y_658_ = v___y_673_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_674_;
goto v___jp_648_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_678_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_665_);
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___y_614_ = v___y_663_;
v___y_615_ = v___y_664_;
v___y_616_ = v___y_666_;
v___y_617_ = v___y_667_;
v___y_618_ = v___y_668_;
v___y_619_ = v___y_669_;
v___y_620_ = v___y_670_;
v___y_621_ = v___y_671_;
v___y_622_ = v___y_672_;
v___y_623_ = v___y_673_;
v___y_624_ = v___y_675_;
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
v___y_663_ = v___y_687_;
v___y_664_ = v___y_690_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_683_;
v___y_667_ = v___y_684_;
v___y_668_ = v___y_685_;
v___y_669_ = v___y_686_;
v___y_670_ = v___y_694_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_691_;
v___y_673_ = v___y_692_;
v___y_674_ = v___y_693_;
v___y_675_ = v___x_695_;
goto v___jp_662_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_663_ = v___y_687_;
v___y_664_ = v___y_690_;
v___y_665_ = v___y_689_;
v___y_666_ = v___y_683_;
v___y_667_ = v___y_684_;
v___y_668_ = v___y_685_;
v___y_669_ = v___y_686_;
v___y_670_ = v___y_694_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_691_;
v___y_673_ = v___y_692_;
v___y_674_ = v___y_693_;
v___y_675_ = v___x_696_;
goto v___jp_662_;
}
}
v___jp_697_:
{
lean_object* v___x_709_; uint32_t v___x_710_; 
v___x_709_ = l_Lake_JobAction_verb(v___y_698_, v___y_703_);
v___x_710_ = l_Lake_LogLevel_icon(v___y_699_);
v___y_683_ = v___y_698_;
v___y_684_ = v___y_699_;
v___y_685_ = v___y_700_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_701_;
v___y_688_ = v___y_705_;
v___y_689_ = v___y_704_;
v___y_690_ = v___y_708_;
v___y_691_ = v___y_706_;
v___y_692_ = v___x_709_;
v___y_693_ = v___y_707_;
v___y_694_ = v___x_710_;
goto v___jp_682_;
}
v___jp_711_:
{
if (v___y_722_ == 0)
{
lean_dec(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_714_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_491_ = v___y_716_;
goto v___jp_490_;
}
else
{
if (v___y_721_ == 0)
{
lean_object* v___x_723_; uint32_t v___x_724_; 
v___x_723_ = l_Lake_JobAction_verb(v___y_712_, v___y_717_);
v___x_724_ = 10004;
v___y_683_ = v___y_712_;
v___y_684_ = v___y_713_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_718_;
v___y_689_ = v___y_719_;
v___y_690_ = v___y_722_;
v___y_691_ = v___y_720_;
v___y_692_ = v___x_723_;
v___y_693_ = v___y_721_;
v___y_694_ = v___x_724_;
goto v___jp_682_;
}
else
{
v___y_698_ = v___y_712_;
v___y_699_ = v___y_713_;
v___y_700_ = v___y_714_;
v___y_701_ = v___y_716_;
v___y_702_ = v___y_715_;
v___y_703_ = v___y_717_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_718_;
v___y_706_ = v___y_720_;
v___y_707_ = v___y_721_;
v___y_708_ = v___y_722_;
goto v___jp_697_;
}
}
}
v___jp_725_:
{
if (v___y_737_ == 0)
{
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v___y_728_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_491_ = v___y_730_;
goto v___jp_490_;
}
else
{
if (v___y_736_ == 0)
{
if (v_showProgress_507_ == 0)
{
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v___y_728_);
lean_dec_ref(v_caption_611_);
lean_dec(v_totalJobs_495_);
lean_dec(v_jobNo_494_);
v___y_491_ = v___y_730_;
goto v___jp_490_;
}
else
{
uint8_t v___x_738_; 
v___x_738_ = lean_bool_not(v_useAnsi_506_);
if (v___x_738_ == 0)
{
v___y_712_ = v___y_726_;
v___y_713_ = v___y_727_;
v___y_714_ = v___y_728_;
v___y_715_ = v___y_729_;
v___y_716_ = v___y_730_;
v___y_717_ = v___y_732_;
v___y_718_ = v___y_734_;
v___y_719_ = v___y_733_;
v___y_720_ = v___y_735_;
v___y_721_ = v___y_736_;
v___y_722_ = v___x_738_;
goto v___jp_711_;
}
else
{
v___y_712_ = v___y_726_;
v___y_713_ = v___y_727_;
v___y_714_ = v___y_728_;
v___y_715_ = v___y_729_;
v___y_716_ = v___y_730_;
v___y_717_ = v___y_732_;
v___y_718_ = v___y_734_;
v___y_719_ = v___y_733_;
v___y_720_ = v___y_735_;
v___y_721_ = v___y_736_;
v___y_722_ = v___y_731_;
goto v___jp_711_;
}
}
}
else
{
v___y_698_ = v___y_726_;
v___y_699_ = v___y_727_;
v___y_700_ = v___y_728_;
v___y_701_ = v___y_730_;
v___y_702_ = v___y_729_;
v___y_703_ = v___y_732_;
v___y_704_ = v___y_733_;
v___y_705_ = v___y_734_;
v___y_706_ = v___y_735_;
v___y_707_ = v___y_736_;
v___y_708_ = v___y_736_;
goto v___jp_697_;
}
}
}
v___jp_739_:
{
uint8_t v___x_751_; 
v___x_751_ = lean_bool_not(v_optional_612_);
if (v___x_751_ == 0)
{
v___y_726_ = v___y_740_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_742_;
v___y_729_ = v___y_743_;
v___y_730_ = v___y_744_;
v___y_731_ = v___y_745_;
v___y_732_ = v___y_746_;
v___y_733_ = v___y_748_;
v___y_734_ = v___y_747_;
v___y_735_ = v___y_749_;
v___y_736_ = v___y_750_;
v___y_737_ = v_showOptional_505_;
goto v___jp_725_;
}
else
{
v___y_726_ = v___y_740_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_742_;
v___y_729_ = v___y_743_;
v___y_730_ = v___y_744_;
v___y_731_ = v___y_745_;
v___y_732_ = v___y_746_;
v___y_733_ = v___y_748_;
v___y_734_ = v___y_747_;
v___y_735_ = v___y_749_;
v___y_736_ = v___y_750_;
v___y_737_ = v___x_751_;
goto v___jp_725_;
}
}
v___jp_752_:
{
if (v___y_753_ == 0)
{
if (v___y_758_ == 0)
{
v___y_740_ = v___y_753_;
v___y_741_ = v___y_754_;
v___y_742_ = v___y_755_;
v___y_743_ = v___y_763_;
v___y_744_ = v___y_764_;
v___y_745_ = v___y_756_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_759_;
v___y_748_ = v___y_760_;
v___y_749_ = v___y_761_;
v___y_750_ = v___y_758_;
goto v___jp_739_;
}
else
{
v___y_740_ = v___y_753_;
v___y_741_ = v___y_754_;
v___y_742_ = v___y_755_;
v___y_743_ = v___y_763_;
v___y_744_ = v___y_764_;
v___y_745_ = v___y_756_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_759_;
v___y_748_ = v___y_760_;
v___y_749_ = v___y_761_;
v___y_750_ = v___y_762_;
goto v___jp_739_;
}
}
else
{
uint8_t v___x_765_; 
v___x_765_ = lean_bool_not(v_optional_612_);
if (v___x_765_ == 0)
{
v___y_740_ = v___y_753_;
v___y_741_ = v___y_754_;
v___y_742_ = v___y_755_;
v___y_743_ = v___y_763_;
v___y_744_ = v___y_764_;
v___y_745_ = v___y_756_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_759_;
v___y_748_ = v___y_760_;
v___y_749_ = v___y_761_;
v___y_750_ = v___y_753_;
goto v___jp_739_;
}
else
{
lean_object* v_jobNo_766_; lean_object* v_totalJobs_767_; uint8_t v_wantsRebuild_768_; lean_object* v_failures_769_; lean_object* v_resetCtrl_770_; lean_object* v_lastUpdate_771_; lean_object* v_spinnerIdx_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
v_jobNo_766_ = lean_ctor_get(v___y_764_, 0);
v_totalJobs_767_ = lean_ctor_get(v___y_764_, 1);
v_wantsRebuild_768_ = lean_ctor_get_uint8(v___y_764_, sizeof(void*)*6);
v_failures_769_ = lean_ctor_get(v___y_764_, 2);
v_resetCtrl_770_ = lean_ctor_get(v___y_764_, 3);
v_lastUpdate_771_ = lean_ctor_get(v___y_764_, 4);
v_spinnerIdx_772_ = lean_ctor_get(v___y_764_, 5);
v_isSharedCheck_780_ = !lean_is_exclusive(v___y_764_);
if (v_isSharedCheck_780_ == 0)
{
v___x_774_ = v___y_764_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_spinnerIdx_772_);
lean_inc(v_lastUpdate_771_);
lean_inc(v_resetCtrl_770_);
lean_inc(v_failures_769_);
lean_inc(v_totalJobs_767_);
lean_inc(v_jobNo_766_);
lean_dec(v___y_764_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
lean_inc_ref(v_caption_611_);
v___x_776_ = lean_array_push(v_failures_769_, v_caption_611_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 2, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_jobNo_766_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_totalJobs_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_resetCtrl_770_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_lastUpdate_771_);
lean_ctor_set(v_reuseFailAlloc_779_, 5, v_spinnerIdx_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*6, v_wantsRebuild_768_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v___y_740_ = v___y_753_;
v___y_741_ = v___y_754_;
v___y_742_ = v___y_755_;
v___y_743_ = v___y_763_;
v___y_744_ = v___x_778_;
v___y_745_ = v___y_756_;
v___y_746_ = v___y_757_;
v___y_747_ = v___y_759_;
v___y_748_ = v___y_760_;
v___y_749_ = v___y_761_;
v___y_750_ = v___y_753_;
goto v___jp_739_;
}
}
}
}
}
v___jp_781_:
{
if (v___y_789_ == 0)
{
v___y_753_ = v___y_782_;
v___y_754_ = v___y_783_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_792_;
v___y_757_ = v___y_785_;
v___y_758_ = v___y_786_;
v___y_759_ = v___y_787_;
v___y_760_ = v___y_788_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
v___y_763_ = v_a_471_;
v___y_764_ = v_a_472_;
goto v___jp_752_;
}
else
{
if (v_wantsRebuild_496_ == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_inc(v_spinnerIdx_500_);
lean_inc(v_lastUpdate_499_);
lean_inc_ref(v_resetCtrl_498_);
lean_inc_ref(v_failures_497_);
v_isSharedCheck_799_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; 
v_unused_800_ = lean_ctor_get(v_a_472_, 5);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_a_472_, 4);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_a_472_, 3);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_a_472_, 2);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_a_472_, 1);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_a_472_, 0);
lean_dec(v_unused_805_);
v___x_794_ = v_a_472_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_dec(v_a_472_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
lean_inc(v_totalJobs_495_);
lean_inc(v_jobNo_494_);
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_jobNo_494_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_totalJobs_495_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_failures_497_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_resetCtrl_498_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_lastUpdate_499_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v_spinnerIdx_500_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*6, v___y_789_);
v___y_753_ = v___y_782_;
v___y_754_ = v___y_783_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_792_;
v___y_757_ = v___y_785_;
v___y_758_ = v___y_786_;
v___y_759_ = v___y_787_;
v___y_760_ = v___y_788_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
v___y_763_ = v_a_471_;
v___y_764_ = v___x_797_;
goto v___jp_752_;
}
}
}
else
{
v___y_753_ = v___y_782_;
v___y_754_ = v___y_783_;
v___y_755_ = v___y_784_;
v___y_756_ = v___y_792_;
v___y_757_ = v___y_785_;
v___y_758_ = v___y_786_;
v___y_759_ = v___y_787_;
v___y_760_ = v___y_788_;
v___y_761_ = v___y_790_;
v___y_762_ = v___y_791_;
v___y_763_ = v_a_471_;
v___y_764_ = v_a_472_;
goto v___jp_752_;
}
}
}
v___jp_806_:
{
uint8_t v___x_817_; 
v___x_817_ = l_Lake_instOrdJobAction_ord(v_minAction_504_, v___y_810_);
if (v___x_817_ == 2)
{
uint8_t v___x_818_; 
v___x_818_ = 0;
v___y_782_ = v___y_807_;
v___y_783_ = v___y_808_;
v___y_784_ = v___y_809_;
v___y_785_ = v___y_810_;
v___y_786_ = v___y_811_;
v___y_787_ = v___y_813_;
v___y_788_ = v___y_812_;
v___y_789_ = v___y_815_;
v___y_790_ = v___y_814_;
v___y_791_ = v___y_816_;
v___y_792_ = v___x_818_;
goto v___jp_781_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = 1;
v___y_782_ = v___y_807_;
v___y_783_ = v___y_808_;
v___y_784_ = v___y_809_;
v___y_785_ = v___y_810_;
v___y_786_ = v___y_811_;
v___y_787_ = v___y_813_;
v___y_788_ = v___y_812_;
v___y_789_ = v___y_815_;
v___y_790_ = v___y_814_;
v___y_791_ = v___y_816_;
v___y_792_ = v___x_819_;
goto v___jp_781_;
}
}
v___jp_820_:
{
uint8_t v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_strict_and(v___y_824_, v___y_829_);
v___x_831_ = l_Lake_instOrdLogLevel_ord(v_outLv_502_, v___y_821_);
if (v___x_831_ == 2)
{
uint8_t v___x_832_; 
v___x_832_ = 0;
v___y_807_ = v___x_830_;
v___y_808_ = v___y_821_;
v___y_809_ = v___y_822_;
v___y_810_ = v___y_823_;
v___y_811_ = v___y_824_;
v___y_812_ = v___y_826_;
v___y_813_ = v___y_825_;
v___y_814_ = v___y_828_;
v___y_815_ = v___y_827_;
v___y_816_ = v___x_832_;
goto v___jp_806_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = 1;
v___y_807_ = v___x_830_;
v___y_808_ = v___y_821_;
v___y_809_ = v___y_822_;
v___y_810_ = v___y_823_;
v___y_811_ = v___y_824_;
v___y_812_ = v___y_826_;
v___y_813_ = v___y_825_;
v___y_814_ = v___y_828_;
v___y_815_ = v___y_827_;
v___y_816_ = v___x_833_;
goto v___jp_806_;
}
}
v___jp_834_:
{
uint8_t v___x_843_; 
v___x_843_ = l_Lake_instOrdLogLevel_ord(v_failLv_503_, v___y_835_);
if (v___x_843_ == 2)
{
uint8_t v___x_844_; 
v___x_844_ = 0;
v___y_821_ = v___y_835_;
v___y_822_ = v___y_836_;
v___y_823_ = v___y_837_;
v___y_824_ = v___y_842_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_838_;
v___y_827_ = v___y_841_;
v___y_828_ = v___y_840_;
v___y_829_ = v___x_844_;
goto v___jp_820_;
}
else
{
uint8_t v___x_845_; 
v___x_845_ = 1;
v___y_821_ = v___y_835_;
v___y_822_ = v___y_836_;
v___y_823_ = v___y_837_;
v___y_824_ = v___y_842_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_838_;
v___y_827_ = v___y_841_;
v___y_828_ = v___y_840_;
v___y_829_ = v___x_845_;
goto v___jp_820_;
}
}
v___jp_846_:
{
lean_object* v_log_848_; uint8_t v_action_849_; uint8_t v_wantsRebuild_850_; lean_object* v_buildTime_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_log_848_ = lean_ctor_get(v___y_847_, 0);
lean_inc_ref(v_log_848_);
v_action_849_ = lean_ctor_get_uint8(v___y_847_, sizeof(void*)*3);
v_wantsRebuild_850_ = lean_ctor_get_uint8(v___y_847_, sizeof(void*)*3 + 1);
v_buildTime_851_ = lean_ctor_get(v___y_847_, 2);
lean_inc(v_buildTime_851_);
lean_dec_ref(v___y_847_);
v___x_852_ = l_Lake_Log_maxLv(v_log_848_);
v___x_853_ = lean_array_get_size(v_log_848_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_nat_dec_eq(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; 
v___x_856_ = 1;
v___y_835_ = v___x_852_;
v___y_836_ = v___x_854_;
v___y_837_ = v_action_849_;
v___y_838_ = v_buildTime_851_;
v___y_839_ = v_log_848_;
v___y_840_ = v___x_853_;
v___y_841_ = v_wantsRebuild_850_;
v___y_842_ = v___x_856_;
goto v___jp_834_;
}
else
{
uint8_t v___x_857_; 
v___x_857_ = 0;
v___y_835_ = v___x_852_;
v___y_836_ = v___x_854_;
v___y_837_ = v_action_849_;
v___y_838_ = v_buildTime_851_;
v___y_839_ = v_log_848_;
v___y_840_ = v___x_853_;
v___y_841_ = v_wantsRebuild_850_;
v___y_842_ = v___x_857_;
goto v___jp_834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_860_, v_a_861_, v_a_862_);
lean_dec_ref(v_a_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_865_, uint8_t v___y_866_, uint8_t v_useAnsi_867_, lean_object* v_as_868_, size_t v_i_869_, size_t v_stop_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_865_, v___y_866_, v_useAnsi_867_, v_as_868_, v_i_869_, v_stop_870_, v_b_871_, v___y_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_876_, lean_object* v___y_877_, lean_object* v_useAnsi_878_, lean_object* v_as_879_, lean_object* v_i_880_, lean_object* v_stop_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v___y_17093__boxed_886_; uint8_t v_useAnsi_17094__boxed_887_; size_t v_i_boxed_888_; size_t v_stop_boxed_889_; lean_object* v_res_890_; 
v___y_17093__boxed_886_ = lean_unbox(v___y_877_);
v_useAnsi_17094__boxed_887_ = lean_unbox(v_useAnsi_878_);
v_i_boxed_888_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_stop_boxed_889_ = lean_unbox_usize(v_stop_881_);
lean_dec(v_stop_881_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_876_, v___y_17093__boxed_886_, v_useAnsi_17094__boxed_887_, v_as_879_, v_i_boxed_888_, v_stop_boxed_889_, v_b_882_, v___y_883_, v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec_ref(v_as_879_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_jobs_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_jobNo_898_; lean_object* v_totalJobs_899_; uint8_t v_wantsRebuild_900_; lean_object* v_failures_901_; lean_object* v_resetCtrl_902_; lean_object* v_lastUpdate_903_; lean_object* v_spinnerIdx_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_jobs_894_ = lean_ctor_get(v_a_891_, 0);
v___x_895_ = lean_st_ref_take(v_jobs_894_);
v___x_896_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_897_ = lean_st_ref_set(v_jobs_894_, v___x_896_);
v_jobNo_898_ = lean_ctor_get(v_a_892_, 0);
v_totalJobs_899_ = lean_ctor_get(v_a_892_, 1);
v_wantsRebuild_900_ = lean_ctor_get_uint8(v_a_892_, sizeof(void*)*6);
v_failures_901_ = lean_ctor_get(v_a_892_, 2);
v_resetCtrl_902_ = lean_ctor_get(v_a_892_, 3);
v_lastUpdate_903_ = lean_ctor_get(v_a_892_, 4);
v_spinnerIdx_904_ = lean_ctor_get(v_a_892_, 5);
v_isSharedCheck_914_ = !lean_is_exclusive(v_a_892_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v_a_892_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_spinnerIdx_904_);
lean_inc(v_lastUpdate_903_);
lean_inc(v_resetCtrl_902_);
lean_inc(v_failures_901_);
lean_inc(v_totalJobs_899_);
lean_inc(v_jobNo_898_);
lean_dec(v_a_892_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_908_ = lean_array_get_size(v___x_895_);
v___x_909_ = lean_nat_add(v_totalJobs_899_, v___x_908_);
lean_dec(v_totalJobs_899_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_909_);
v___x_911_ = v___x_906_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_jobNo_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_failures_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_resetCtrl_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_lastUpdate_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_spinnerIdx_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_913_, sizeof(void*)*6, v_wantsRebuild_900_);
v___x_911_ = v_reuseFailAlloc_913_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_895_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_915_, v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object* v_as_919_, size_t v_i_920_, size_t v_stop_921_, lean_object* v_b_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_fst_927_; lean_object* v_snd_928_; uint8_t v___x_932_; 
v___x_932_ = lean_usize_dec_eq(v_i_920_, v_stop_921_);
if (v___x_932_ == 0)
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_935_; lean_object* v_task_936_; uint8_t v___x_937_; 
v_fst_933_ = lean_ctor_get(v_b_922_, 0);
v_snd_934_ = lean_ctor_get(v_b_922_, 1);
v___x_935_ = lean_array_uget_borrowed(v_as_919_, v_i_920_);
v_task_936_ = lean_ctor_get(v___x_935_, 0);
v___x_937_ = lean_io_get_task_state(v_task_936_);
switch(v___x_937_)
{
case 0:
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_945_; 
lean_inc(v_snd_934_);
lean_inc(v_fst_933_);
v_isSharedCheck_945_ = !lean_is_exclusive(v_b_922_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; lean_object* v_unused_947_; 
v_unused_946_ = lean_ctor_get(v_b_922_, 1);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_b_922_, 0);
lean_dec(v_unused_947_);
v___x_939_ = v_b_922_;
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
else
{
lean_dec(v_b_922_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_945_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_inc(v___x_935_);
v___x_941_ = lean_array_push(v_snd_934_, v___x_935_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_fst_933_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
v_fst_927_ = v___x_943_;
v_snd_928_ = v___y_924_;
goto v___jp_926_;
}
}
}
case 1:
{
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_956_; 
lean_inc(v_snd_934_);
lean_inc(v_fst_933_);
v_isSharedCheck_956_ = !lean_is_exclusive(v_b_922_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_957_ = lean_ctor_get(v_b_922_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_b_922_, 0);
lean_dec(v_unused_958_);
v___x_949_ = v_b_922_;
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
else
{
lean_dec(v_b_922_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_956_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
lean_inc_n(v___x_935_, 2);
v___x_951_ = lean_array_push(v_fst_933_, v___x_935_);
v___x_952_ = lean_array_push(v_snd_934_, v___x_935_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___x_952_);
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_fst_927_ = v___x_954_;
v_snd_928_ = v___y_924_;
goto v___jp_926_;
}
}
}
default: 
{
lean_object* v___x_959_; lean_object* v_snd_960_; lean_object* v_jobNo_961_; lean_object* v_totalJobs_962_; uint8_t v_wantsRebuild_963_; lean_object* v_failures_964_; lean_object* v_resetCtrl_965_; lean_object* v_lastUpdate_966_; lean_object* v_spinnerIdx_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_976_; 
lean_inc(v___x_935_);
v___x_959_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_935_, v___y_923_, v___y_924_);
v_snd_960_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_snd_960_);
lean_dec_ref(v___x_959_);
v_jobNo_961_ = lean_ctor_get(v_snd_960_, 0);
v_totalJobs_962_ = lean_ctor_get(v_snd_960_, 1);
v_wantsRebuild_963_ = lean_ctor_get_uint8(v_snd_960_, sizeof(void*)*6);
v_failures_964_ = lean_ctor_get(v_snd_960_, 2);
v_resetCtrl_965_ = lean_ctor_get(v_snd_960_, 3);
v_lastUpdate_966_ = lean_ctor_get(v_snd_960_, 4);
v_spinnerIdx_967_ = lean_ctor_get(v_snd_960_, 5);
v_isSharedCheck_976_ = !lean_is_exclusive(v_snd_960_);
if (v_isSharedCheck_976_ == 0)
{
v___x_969_ = v_snd_960_;
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_spinnerIdx_967_);
lean_inc(v_lastUpdate_966_);
lean_inc(v_resetCtrl_965_);
lean_inc(v_failures_964_);
lean_inc(v_totalJobs_962_);
lean_inc(v_jobNo_961_);
lean_dec(v_snd_960_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_jobNo_961_, v___x_971_);
lean_dec(v_jobNo_961_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_totalJobs_962_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_failures_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_resetCtrl_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_lastUpdate_966_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v_spinnerIdx_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*6, v_wantsRebuild_963_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
v_fst_927_ = v_b_922_;
v_snd_928_ = v___x_974_;
goto v___jp_926_;
}
}
}
}
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_b_922_);
lean_ctor_set(v___x_977_, 1, v___y_924_);
return v___x_977_;
}
v___jp_926_:
{
size_t v___x_929_; size_t v___x_930_; 
v___x_929_ = ((size_t)1ULL);
v___x_930_ = lean_usize_add(v_i_920_, v___x_929_);
v_i_920_ = v___x_930_;
v_b_922_ = v_fst_927_;
v___y_924_ = v_snd_928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object* v_as_978_, lean_object* v_i_979_, lean_object* v_stop_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
size_t v_i_boxed_985_; size_t v_stop_boxed_986_; lean_object* v_res_987_; 
v_i_boxed_985_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_stop_boxed_986_ = lean_unbox_usize(v_stop_980_);
lean_dec(v_stop_980_);
v_res_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_978_, v_i_boxed_985_, v_stop_boxed_986_, v_b_981_, v___y_982_, v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_as_978_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object* v_new_990_, lean_object* v_unfinished_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v___y_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___y_1010_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_1013_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_1014_ = lean_array_get_size(v_unfinished_991_);
v___x_1015_ = lean_nat_dec_lt(v___x_995_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_inc_ref(v_a_993_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v_a_993_);
v___y_997_ = v___x_1016_;
v_fst_998_ = v___x_1013_;
v_snd_999_ = v_a_993_;
goto v___jp_996_;
}
else
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_nat_dec_le(v___x_1014_, v___x_1014_);
if (v___x_1017_ == 0)
{
if (v___x_1015_ == 0)
{
lean_object* v___x_1018_; 
lean_inc_ref(v_a_993_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1013_);
lean_ctor_set(v___x_1018_, 1, v_a_993_);
v___y_997_ = v___x_1018_;
v_fst_998_ = v___x_1013_;
v_snd_999_ = v_a_993_;
goto v___jp_996_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1014_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_991_, v___x_1019_, v___x_1020_, v___x_1013_, v_a_992_, v_a_993_);
v___y_1010_ = v___x_1021_;
goto v___jp_1009_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1014_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_991_, v___x_1022_, v___x_1023_, v___x_1013_, v_a_992_, v_a_993_);
v___y_1010_ = v___x_1024_;
goto v___jp_1009_;
}
}
v___jp_996_:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_array_get_size(v_new_990_);
v___x_1001_ = lean_nat_dec_lt(v___x_995_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_snd_999_);
lean_dec_ref(v_fst_998_);
return v___y_997_;
}
else
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_nat_dec_le(v___x_1000_, v___x_1000_);
if (v___x_1002_ == 0)
{
if (v___x_1001_ == 0)
{
lean_dec_ref(v_snd_999_);
lean_dec_ref(v_fst_998_);
return v___y_997_;
}
else
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
lean_dec_ref(v___y_997_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = lean_usize_of_nat(v___x_1000_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_990_, v___x_1003_, v___x_1004_, v_fst_998_, v_a_992_, v_snd_999_);
return v___x_1005_;
}
}
else
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___y_997_);
v___x_1006_ = ((size_t)0ULL);
v___x_1007_ = lean_usize_of_nat(v___x_1000_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_990_, v___x_1006_, v___x_1007_, v_fst_998_, v_a_992_, v_snd_999_);
return v___x_1008_;
}
}
}
v___jp_1009_:
{
lean_object* v_fst_1011_; lean_object* v_snd_1012_; 
v_fst_1011_ = lean_ctor_get(v___y_1010_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v___y_1010_, 1);
lean_inc(v_snd_1012_);
v___y_997_ = v___y_1010_;
v_fst_998_ = v_fst_1011_;
v_snd_999_ = v_snd_1012_;
goto v___jp_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_1025_, lean_object* v_unfinished_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1025_, v_unfinished_1026_, v_a_1027_, v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec_ref(v_unfinished_1026_);
lean_dec_ref(v_new_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___y_1035_; lean_object* v___x_1053_; lean_object* v_lastUpdate_1054_; lean_object* v_updateFrequency_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1053_ = lean_io_mono_ms_now();
v_lastUpdate_1054_ = lean_ctor_get(v_a_1032_, 4);
v_updateFrequency_1055_ = lean_ctor_get(v_a_1031_, 2);
v___x_1056_ = lean_nat_sub(v___x_1053_, v_lastUpdate_1054_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_nat_sub(v_updateFrequency_1055_, v___x_1056_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_nat_dec_lt(v___x_1058_, v___x_1057_);
if (v___x_1059_ == 0)
{
lean_dec(v___x_1057_);
v___y_1035_ = v_a_1032_;
goto v___jp_1034_;
}
else
{
uint32_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_uint32_of_nat(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1061_ = l_IO_sleep(v___x_1060_);
v___y_1035_ = v_a_1032_;
goto v___jp_1034_;
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v_jobNo_1037_; lean_object* v_totalJobs_1038_; uint8_t v_wantsRebuild_1039_; lean_object* v_failures_1040_; lean_object* v_resetCtrl_1041_; lean_object* v_spinnerIdx_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v___x_1036_ = lean_io_mono_ms_now();
v_jobNo_1037_ = lean_ctor_get(v___y_1035_, 0);
v_totalJobs_1038_ = lean_ctor_get(v___y_1035_, 1);
v_wantsRebuild_1039_ = lean_ctor_get_uint8(v___y_1035_, sizeof(void*)*6);
v_failures_1040_ = lean_ctor_get(v___y_1035_, 2);
v_resetCtrl_1041_ = lean_ctor_get(v___y_1035_, 3);
v_spinnerIdx_1042_ = lean_ctor_get(v___y_1035_, 5);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___y_1035_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v___y_1035_, 4);
lean_dec(v_unused_1052_);
v___x_1044_ = v___y_1035_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_spinnerIdx_1042_);
lean_inc(v_resetCtrl_1041_);
lean_inc(v_failures_1040_);
lean_inc(v_totalJobs_1038_);
lean_inc(v_jobNo_1037_);
lean_dec(v___y_1035_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_box(0);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 4, v___x_1036_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_jobNo_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_totalJobs_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_failures_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_resetCtrl_1041_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_spinnerIdx_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*6, v_wantsRebuild_1039_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1046_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1062_, v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_1066_, lean_object* v_unfinished_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1071_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1066_, v_unfinished_1067_, v_a_1068_, v_a_1069_);
lean_dec_ref(v_unfinished_1067_);
lean_dec_ref(v_new_1066_);
v_fst_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_fst_1072_);
v_snd_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_snd_1073_);
lean_dec_ref(v___x_1071_);
v_fst_1074_ = lean_ctor_get(v_fst_1072_, 0);
lean_inc(v_fst_1074_);
v_snd_1075_ = lean_ctor_get(v_fst_1072_, 1);
lean_inc(v_snd_1075_);
lean_dec(v_fst_1072_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_array_get_size(v_snd_1075_);
v___x_1078_ = lean_nat_dec_lt(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_fst_1074_);
v___x_1079_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1068_, v_snd_1073_);
v_fst_1080_ = lean_ctor_get(v___x_1079_, 0);
v_snd_1081_ = lean_ctor_get(v___x_1079_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1083_ = v___x_1079_;
v_isShared_1084_ = v_isSharedCheck_1092_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_inc(v_fst_1080_);
lean_dec(v___x_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1092_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_array_get_size(v_fst_1080_);
v___x_1086_ = lean_nat_dec_lt(v___x_1076_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_fst_1080_);
lean_dec(v_snd_1075_);
v___x_1087_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1087_);
v___x_1089_ = v___x_1083_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1081_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_del_object(v___x_1083_);
v_new_1066_ = v_fst_1080_;
v_unfinished_1067_ = v_snd_1075_;
v_a_1069_ = v_snd_1081_;
goto _start;
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v_snd_1094_; lean_object* v___x_1095_; lean_object* v_snd_1096_; lean_object* v___x_1097_; lean_object* v_fst_1098_; lean_object* v_snd_1099_; 
v___x_1093_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1074_, v_snd_1075_, v_a_1068_, v_snd_1073_);
lean_dec(v_fst_1074_);
v_snd_1094_ = lean_ctor_get(v___x_1093_, 1);
lean_inc(v_snd_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1068_, v_snd_1094_);
v_snd_1096_ = lean_ctor_get(v___x_1095_, 1);
lean_inc(v_snd_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1068_, v_snd_1096_);
v_fst_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_fst_1098_);
v_snd_1099_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_snd_1099_);
lean_dec_ref(v___x_1097_);
v_new_1066_ = v_fst_1098_;
v_unfinished_1067_ = v_snd_1075_;
v_a_1069_ = v_snd_1099_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1101_, lean_object* v_unfinished_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1101_, v_unfinished_1102_, v_a_1103_, v_a_1104_);
lean_dec_ref(v_a_1103_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1182_; 
v___x_1111_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1108_, v_a_1109_);
v_fst_1112_ = lean_ctor_get(v___x_1111_, 0);
v_snd_1113_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1115_ = v___x_1111_;
v_isShared_1116_ = v_isSharedCheck_1182_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_snd_1113_);
lean_inc(v_fst_1112_);
lean_dec(v___x_1111_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1182_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v_snd_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1180_; 
v___x_1117_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1112_, v_init_1107_, v_a_1108_, v_snd_1113_);
v_snd_1118_ = lean_ctor_get(v___x_1117_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v___x_1117_, 0);
lean_dec(v_unused_1181_);
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1180_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_snd_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1180_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_jobNo_1122_; lean_object* v_totalJobs_1123_; uint8_t v_wantsRebuild_1124_; lean_object* v_failures_1125_; lean_object* v_resetCtrl_1126_; lean_object* v_lastUpdate_1127_; lean_object* v_spinnerIdx_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1179_; 
v_jobNo_1122_ = lean_ctor_get(v_snd_1118_, 0);
v_totalJobs_1123_ = lean_ctor_get(v_snd_1118_, 1);
v_wantsRebuild_1124_ = lean_ctor_get_uint8(v_snd_1118_, sizeof(void*)*6);
v_failures_1125_ = lean_ctor_get(v_snd_1118_, 2);
v_resetCtrl_1126_ = lean_ctor_get(v_snd_1118_, 3);
v_lastUpdate_1127_ = lean_ctor_get(v_snd_1118_, 4);
v_spinnerIdx_1128_ = lean_ctor_get(v_snd_1118_, 5);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_snd_1118_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1130_ = v_snd_1118_;
v_isShared_1131_ = v_isSharedCheck_1179_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_spinnerIdx_1128_);
lean_inc(v_lastUpdate_1127_);
lean_inc(v_resetCtrl_1126_);
lean_inc(v_failures_1125_);
lean_inc(v_totalJobs_1123_);
lean_inc(v_jobNo_1122_);
lean_dec(v_snd_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1179_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 3, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_jobNo_1122_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_totalJobs_1123_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_failures_1125_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v_lastUpdate_1127_);
lean_ctor_set(v_reuseFailAlloc_1178_, 5, v_spinnerIdx_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1178_, sizeof(void*)*6, v_wantsRebuild_1124_);
v___x_1134_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v_val_1136_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_string_utf8_byte_size(v_resetCtrl_1126_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_nat_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v_out_1143_; lean_object* v_flush_1144_; lean_object* v_putStr_1145_; lean_object* v___x_1150_; 
lean_del_object(v___x_1115_);
v_out_1143_ = lean_ctor_get(v_a_1108_, 1);
v_flush_1144_ = lean_ctor_get(v_out_1143_, 0);
v_putStr_1145_ = lean_ctor_get(v_out_1143_, 4);
lean_inc_ref(v_putStr_1145_);
lean_inc_ref(v_resetCtrl_1126_);
v___x_1150_ = lean_apply_2(v_putStr_1145_, v_resetCtrl_1126_, lean_box(0));
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_dec_ref_known(v___x_1150_, 1);
lean_dec_ref(v_resetCtrl_1126_);
goto v___jp_1146_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1173_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1173_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1173_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1155_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1156_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1157_ = lean_unsigned_to_nat(89u);
v___x_1158_ = lean_unsigned_to_nat(4u);
v___x_1159_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1160_ = lean_io_error_to_string(v_a_1151_);
v___x_1161_ = lean_string_append(v___x_1159_, v___x_1160_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1163_ = lean_string_append(v___x_1161_, v___x_1162_);
v___x_1164_ = l_String_quote(v_resetCtrl_1126_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 3);
lean_ctor_set(v___x_1153_, 0, v___x_1164_);
v___x_1166_ = v___x_1153_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1167_ = l_Std_Format_defWidth;
v___x_1168_ = l_Std_Format_pretty(v___x_1166_, v___x_1167_, v___x_1141_, v___x_1141_);
v___x_1169_ = lean_string_append(v___x_1163_, v___x_1168_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = l_mkPanicMessageWithDecl(v___x_1155_, v___x_1156_, v___x_1157_, v___x_1158_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1170_);
goto v___jp_1146_;
}
}
}
v___jp_1146_:
{
lean_object* v___x_1147_; 
lean_inc_ref(v_flush_1144_);
v___x_1147_ = lean_apply_1(v_flush_1144_, lean_box(0));
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v_val_1136_ = v_a_1148_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = lean_box(0);
v_val_1136_ = v___x_1149_;
goto v___jp_1135_;
}
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_dec_ref(v_resetCtrl_1126_);
lean_del_object(v___x_1120_);
v___x_1174_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v___x_1134_);
lean_ctor_set(v___x_1115_, 0, v___x_1174_);
v___x_1176_ = v___x_1115_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1134_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
v___jp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1134_);
lean_ctor_set(v___x_1120_, 0, v_val_1136_);
v___x_1138_ = v___x_1120_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_val_1136_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1134_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1183_, v_a_1184_, v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1188_){
_start:
{
lean_object* v_failures_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_failures_1189_ = lean_ctor_get(v_self_1188_, 0);
v___x_1190_ = lean_array_get_size(v_failures_1189_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_nat_dec_eq(v___x_1190_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1193_){
_start:
{
uint8_t v_res_1194_; lean_object* v_r_1195_; 
v_res_1194_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1193_);
lean_dec_ref(v_self_1193_);
v_r_1195_ = lean_box(v_res_1194_);
return v_r_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1196_, lean_object* v_jobs_1197_){
_start:
{
lean_object* v_toLogConfig_1199_; uint8_t v_verbosity_1200_; uint8_t v_failLv_1201_; uint8_t v_outLv_1202_; uint8_t v_ansiMode_1203_; lean_object* v_out_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; uint8_t v___x_1207_; uint8_t v___x_1208_; uint8_t v___x_1209_; uint8_t v___y_1211_; uint8_t v___y_1212_; uint8_t v___y_1216_; 
v_toLogConfig_1199_ = lean_ctor_get(v_cfg_1196_, 0);
v_verbosity_1200_ = lean_ctor_get_uint8(v_cfg_1196_, sizeof(void*)*3 + 3);
v_failLv_1201_ = lean_ctor_get_uint8(v_toLogConfig_1199_, sizeof(void*)*1);
v_outLv_1202_ = lean_ctor_get_uint8(v_toLogConfig_1199_, sizeof(void*)*1 + 1);
v_ansiMode_1203_ = lean_ctor_get_uint8(v_toLogConfig_1199_, sizeof(void*)*1 + 2);
v_out_1204_ = lean_ctor_get(v_toLogConfig_1199_, 0);
v___x_1205_ = l_Lake_OutStream_get(v_out_1204_);
lean_inc_ref(v___x_1205_);
v___x_1206_ = l_Lake_AnsiMode_isEnabled(v___x_1205_, v_ansiMode_1203_);
v___x_1207_ = l_Lake_BuildConfig_showProgress(v_cfg_1196_);
v___x_1208_ = 2;
v___x_1209_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1200_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = 3;
v___y_1216_ = v___x_1218_;
goto v___jp_1215_;
}
else
{
uint8_t v___x_1219_; 
v___x_1219_ = 0;
v___y_1216_ = v___x_1219_;
goto v___jp_1215_;
}
v___jp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_unsigned_to_nat(100u);
v___x_1214_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v___x_1214_, 0, v_jobs_1197_);
lean_ctor_set(v___x_1214_, 1, v___x_1205_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3, v_outLv_1202_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 1, v_failLv_1201_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 2, v___y_1211_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 3, v___x_1209_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 4, v___x_1206_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 5, v___x_1207_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 6, v___y_1212_);
return v___x_1214_;
}
v___jp_1215_:
{
if (v___x_1209_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_bool_not(v___x_1206_);
v___y_1211_ = v___y_1216_;
v___y_1212_ = v___x_1217_;
goto v___jp_1210_;
}
else
{
v___y_1211_ = v___y_1216_;
v___y_1212_ = v___x_1209_;
goto v___jp_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1220_, lean_object* v_jobs_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1220_, v_jobs_1221_);
lean_dec_ref(v_cfg_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1224_, lean_object* v_initJobs_1225_, lean_object* v_initFailures_1226_, lean_object* v_resetCtrl_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_snd_1234_; lean_object* v_totalJobs_1235_; uint8_t v_wantsRebuild_1236_; lean_object* v_failures_1237_; lean_object* v___x_1238_; 
v___x_1229_ = lean_io_mono_ms_now();
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = 0;
v___x_1232_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
lean_ctor_set(v___x_1232_, 2, v_initFailures_1226_);
lean_ctor_set(v___x_1232_, 3, v_resetCtrl_1227_);
lean_ctor_set(v___x_1232_, 4, v___x_1229_);
lean_ctor_set(v___x_1232_, 5, v___x_1230_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*6, v___x_1231_);
v___x_1233_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1225_, v_ctx_1224_, v___x_1232_);
v_snd_1234_ = lean_ctor_get(v___x_1233_, 1);
lean_inc(v_snd_1234_);
lean_dec_ref(v___x_1233_);
v_totalJobs_1235_ = lean_ctor_get(v_snd_1234_, 1);
lean_inc(v_totalJobs_1235_);
v_wantsRebuild_1236_ = lean_ctor_get_uint8(v_snd_1234_, sizeof(void*)*6);
v_failures_1237_ = lean_ctor_get(v_snd_1234_, 2);
lean_inc_ref(v_failures_1237_);
lean_dec(v_snd_1234_);
v___x_1238_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1238_, 0, v_failures_1237_);
lean_ctor_set(v___x_1238_, 1, v_totalJobs_1235_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*2, v_wantsRebuild_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1239_, lean_object* v_initJobs_1240_, lean_object* v_initFailures_1241_, lean_object* v_resetCtrl_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1239_, v_initJobs_1240_, v_initFailures_1241_, v_resetCtrl_1242_);
lean_dec_ref(v_ctx_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1245_, lean_object* v_jobs_1246_, lean_object* v_out_1247_, uint8_t v_failLv_1248_, uint8_t v_outLv_1249_, uint8_t v_minAction_1250_, uint8_t v_showOptional_1251_, uint8_t v_useAnsi_1252_, uint8_t v_showProgress_1253_, uint8_t v_showTime_1254_, lean_object* v_resetCtrl_1255_, lean_object* v_initFailures_1256_, lean_object* v_updateFrequency_1257_){
_start:
{
lean_object* v_ctx_1259_; lean_object* v___x_1260_; 
v_ctx_1259_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v_ctx_1259_, 0, v_jobs_1246_);
lean_ctor_set(v_ctx_1259_, 1, v_out_1247_);
lean_ctor_set(v_ctx_1259_, 2, v_updateFrequency_1257_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3, v_outLv_1249_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3 + 1, v_failLv_1248_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3 + 2, v_minAction_1250_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3 + 3, v_showOptional_1251_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3 + 4, v_useAnsi_1252_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3 + 5, v_showProgress_1253_);
lean_ctor_set_uint8(v_ctx_1259_, sizeof(void*)*3 + 6, v_showTime_1254_);
v___x_1260_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1259_, v_initJobs_1245_, v_initFailures_1256_, v_resetCtrl_1255_);
lean_dec_ref_known(v_ctx_1259_, 3);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1261_, lean_object* v_jobs_1262_, lean_object* v_out_1263_, lean_object* v_failLv_1264_, lean_object* v_outLv_1265_, lean_object* v_minAction_1266_, lean_object* v_showOptional_1267_, lean_object* v_useAnsi_1268_, lean_object* v_showProgress_1269_, lean_object* v_showTime_1270_, lean_object* v_resetCtrl_1271_, lean_object* v_initFailures_1272_, lean_object* v_updateFrequency_1273_, lean_object* v_a_1274_){
_start:
{
uint8_t v_failLv_boxed_1275_; uint8_t v_outLv_boxed_1276_; uint8_t v_minAction_boxed_1277_; uint8_t v_showOptional_boxed_1278_; uint8_t v_useAnsi_boxed_1279_; uint8_t v_showProgress_boxed_1280_; uint8_t v_showTime_boxed_1281_; lean_object* v_res_1282_; 
v_failLv_boxed_1275_ = lean_unbox(v_failLv_1264_);
v_outLv_boxed_1276_ = lean_unbox(v_outLv_1265_);
v_minAction_boxed_1277_ = lean_unbox(v_minAction_1266_);
v_showOptional_boxed_1278_ = lean_unbox(v_showOptional_1267_);
v_useAnsi_boxed_1279_ = lean_unbox(v_useAnsi_1268_);
v_showProgress_boxed_1280_ = lean_unbox(v_showProgress_1269_);
v_showTime_boxed_1281_ = lean_unbox(v_showTime_1270_);
v_res_1282_ = l_Lake_monitorJobs(v_initJobs_1261_, v_jobs_1262_, v_out_1263_, v_failLv_boxed_1275_, v_outLv_boxed_1276_, v_minAction_boxed_1277_, v_showOptional_boxed_1278_, v_useAnsi_boxed_1279_, v_showProgress_boxed_1280_, v_showTime_boxed_1281_, v_resetCtrl_1271_, v_initFailures_1272_, v_updateFrequency_1273_);
return v_res_1282_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1283_; 
v___x_1283_ = 3;
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1284_, lean_object* v_x_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_apply_2(v_logger_1284_, v___y_1286_, lean_box(0));
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1289_, v_x_1290_, v___y_1291_);
return v_res_1293_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1296_ = l_String_quote(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1);
v___x_1298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___f_1300_; 
v___x_1299_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_1300_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1300_, 0, v___x_1299_);
return v___f_1300_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6));
v___x_1308_ = l_String_quote(v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_1310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = l_Std_Format_defWidth;
v___x_1313_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
v___x_1314_ = l_Std_Format_pretty(v___x_1313_, v___x_1312_, v___x_1311_, v___x_1311_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10));
v___x_1317_ = l_String_quote(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_1319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = l_Std_Format_defWidth;
v___x_1322_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
v___x_1323_ = l_Std_Format_pretty(v___x_1322_, v___x_1321_, v___x_1320_, v___x_1320_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1325_, lean_object* v_ws_1326_, lean_object* v_outputsRef_x3f_1327_, lean_object* v_out_1328_, lean_object* v_outputsFile_1329_, uint8_t v_isVerbose_1330_){
_start:
{
lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1350_; lean_object* v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___x_1459_; 
lean_inc_ref(v_logger_1325_);
v___f_1332_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1332_, 0, v_logger_1325_);
v___x_1333_ = l_instMonadBaseIO;
v___x_1459_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1326_);
if (v___x_1459_ == 0)
{
lean_object* v_packages_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_baseName_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_packages_1460_ = lean_ctor_get(v_ws_1326_, 4);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_fget_borrowed(v_packages_1460_, v___x_1461_);
v_baseName_1463_ = lean_ctor_get(v___x_1462_, 1);
lean_inc(v_baseName_1463_);
v___x_1464_ = l_Lean_Name_toString(v_baseName_1463_, v___x_1459_);
v___x_1465_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14));
v___x_1466_ = lean_string_append(v___x_1464_, v___x_1465_);
v___x_1467_ = 2;
v___x_1468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*1, v___x_1467_);
v___x_1469_ = lean_apply_2(v_logger_1325_, v___x_1468_, lean_box(0));
goto v___jp_1401_;
}
else
{
lean_dec_ref(v_logger_1325_);
goto v___jp_1401_;
}
v___jp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = lean_array_get_size(v___y_1335_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_nat_dec_lt(v___y_1336_, v___x_1337_);
lean_dec(v___y_1336_);
if (v___x_1339_ == 0)
{
lean_dec_ref(v___y_1335_);
lean_dec_ref(v___f_1332_);
return v___x_1338_;
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_nat_dec_le(v___x_1337_, v___x_1337_);
if (v___x_1340_ == 0)
{
if (v___x_1339_ == 0)
{
lean_dec_ref(v___y_1335_);
lean_dec_ref(v___f_1332_);
return v___x_1338_;
}
else
{
size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1785__overap_1343_; lean_object* v___x_1344_; 
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = lean_usize_of_nat(v___x_1337_);
v___x_1785__overap_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1332_, v___y_1335_, v___x_1341_, v___x_1342_, v___x_1338_);
v___x_1344_ = lean_apply_1(v___x_1785__overap_1343_, lean_box(0));
return v___x_1344_;
}
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1789__overap_1347_; lean_object* v___x_1348_; 
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_of_nat(v___x_1337_);
v___x_1789__overap_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1332_, v___y_1335_, v___x_1345_, v___x_1346_, v___x_1338_);
v___x_1348_ = lean_apply_1(v___x_1789__overap_1347_, lean_box(0));
return v___x_1348_;
}
}
}
v___jp_1349_:
{
if (v___y_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec_ref(v___f_1332_);
lean_dec_ref(v_out_1328_);
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
else
{
lean_object* v_putStr_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_putStr_1354_ = lean_ctor_get(v_out_1328_, 4);
lean_inc_ref(v_putStr_1354_);
lean_dec_ref(v_out_1328_);
v___x_1355_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1356_ = lean_apply_2(v_putStr_1354_, v___x_1355_, lean_box(0));
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
v___y_1335_ = v___y_1350_;
v___y_1336_ = v___y_1351_;
goto v___jp_1334_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1833__overap_1383_; lean_object* v___x_1384_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1359_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1360_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1361_ = lean_unsigned_to_nat(89u);
v___x_1362_ = lean_unsigned_to_nat(4u);
v___x_1363_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1364_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_1365_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc_n(v___y_1351_, 3);
v___x_1366_ = l_Lean_Name_num___override(v___x_1365_, v___y_1351_);
v___x_1367_ = l_Lean_Name_str___override(v___x_1366_, v___x_1364_);
v___x_1368_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_1369_ = l_Lean_Name_str___override(v___x_1367_, v___x_1368_);
v___x_1370_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1369_, v___y_1352_);
v___x_1371_ = lean_string_append(v___x_1363_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
v___x_1374_ = lean_io_error_to_string(v_a_1357_);
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v___x_1378_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2);
v___x_1379_ = l_Std_Format_defWidth;
v___x_1380_ = l_Std_Format_pretty(v___x_1378_, v___x_1379_, v___y_1351_, v___y_1351_);
v___x_1381_ = lean_string_append(v___x_1377_, v___x_1380_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = l_mkPanicMessageWithDecl(v___x_1359_, v___x_1360_, v___x_1361_, v___x_1362_, v___x_1381_);
lean_dec_ref(v___x_1381_);
v___x_1833__overap_1383_ = l_panic___redArg(v___x_1358_, v___x_1382_);
v___x_1384_ = lean_apply_1(v___x_1833__overap_1383_, lean_box(0));
v___y_1335_ = v___y_1350_;
v___y_1336_ = v___y_1351_;
goto v___jp_1334_;
}
}
}
v___jp_1385_:
{
if (v_isVerbose_1330_ == 0)
{
lean_object* v___x_1388_; 
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec_ref(v___f_1332_);
v___x_1388_ = lean_box(0);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_array_get_size(v___y_1386_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_nat_dec_lt(v___y_1387_, v___x_1389_);
lean_dec(v___y_1387_);
if (v___x_1391_ == 0)
{
lean_dec_ref(v___y_1386_);
lean_dec_ref(v___f_1332_);
return v___x_1390_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_le(v___x_1389_, v___x_1389_);
if (v___x_1392_ == 0)
{
if (v___x_1391_ == 0)
{
lean_dec_ref(v___y_1386_);
lean_dec_ref(v___f_1332_);
return v___x_1390_;
}
else
{
size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1859__overap_1395_; lean_object* v___x_1396_; 
v___x_1393_ = ((size_t)0ULL);
v___x_1394_ = lean_usize_of_nat(v___x_1389_);
v___x_1859__overap_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1332_, v___y_1386_, v___x_1393_, v___x_1394_, v___x_1390_);
v___x_1396_ = lean_apply_1(v___x_1859__overap_1395_, lean_box(0));
return v___x_1396_;
}
}
else
{
size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1863__overap_1399_; lean_object* v___x_1400_; 
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_of_nat(v___x_1389_);
v___x_1863__overap_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1332_, v___y_1386_, v___x_1397_, v___x_1398_, v___x_1390_);
v___x_1400_ = lean_apply_1(v___x_1863__overap_1399_, lean_box(0));
return v___x_1400_;
}
}
}
}
v___jp_1401_:
{
if (lean_obj_tag(v_outputsRef_x3f_1327_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1403_; lean_object* v_packages_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_config_1407_; lean_object* v_toLeanConfig_1408_; lean_object* v_platformIndependent_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_val_1402_ = lean_ctor_get(v_outputsRef_x3f_1327_, 0);
v___x_1403_ = lean_st_ref_get(v_val_1402_);
v_packages_1404_ = lean_ctor_get(v_ws_1326_, 4);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_array_fget_borrowed(v_packages_1404_, v___x_1405_);
v_config_1407_ = lean_ctor_get(v___x_1406_, 6);
v_toLeanConfig_1408_ = lean_ctor_get(v_config_1407_, 1);
v_platformIndependent_1409_ = lean_ctor_get(v_toLeanConfig_1408_, 10);
v___f_1410_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3);
v___x_1411_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
lean_inc(v_platformIndependent_1409_);
v___x_1412_ = l_Option_instBEq_beq___redArg(v___f_1410_, v_platformIndependent_1409_, v___x_1411_);
v___x_1413_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_1414_ = l_Lake_CacheMap_writeFile(v_outputsFile_1329_, v___x_1403_, v___x_1412_, v___x_1413_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 2);
v___x_1416_ = lean_array_get_size(v_a_1415_);
v___x_1417_ = lean_nat_dec_eq(v___x_1416_, v___x_1405_);
v___x_1418_ = lean_bool_not(v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1350_ = v_a_1415_;
v___y_1351_ = v___x_1405_;
v___y_1352_ = v___x_1418_;
goto v___jp_1349_;
}
else
{
v___y_1350_ = v_a_1415_;
v___y_1351_ = v___x_1405_;
v___y_1352_ = v_isVerbose_1330_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1419_; lean_object* v_putStr_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_a_1419_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1414_, 2);
v_putStr_1420_ = lean_ctor_get(v_out_1328_, 4);
lean_inc_ref(v_putStr_1420_);
lean_dec_ref(v_out_1328_);
v___x_1421_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6));
v___x_1422_ = lean_apply_2(v_putStr_1420_, v___x_1421_, lean_box(0));
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_dec_ref_known(v___x_1422_, 1);
v___y_1386_ = v_a_1419_;
v___y_1387_ = v___x_1405_;
goto v___jp_1385_;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1754__overap_1437_; lean_object* v___x_1438_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1426_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1427_ = lean_unsigned_to_nat(89u);
v___x_1428_ = lean_unsigned_to_nat(4u);
v___x_1429_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1430_ = lean_io_error_to_string(v_a_1423_);
v___x_1431_ = lean_string_append(v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1433_ = lean_string_append(v___x_1431_, v___x_1432_);
v___x_1434_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_1435_ = lean_string_append(v___x_1433_, v___x_1434_);
v___x_1436_ = l_mkPanicMessageWithDecl(v___x_1425_, v___x_1426_, v___x_1427_, v___x_1428_, v___x_1435_);
lean_dec_ref(v___x_1435_);
v___x_1754__overap_1437_ = l_panic___redArg(v___x_1424_, v___x_1436_);
v___x_1438_ = lean_apply_1(v___x_1754__overap_1437_, lean_box(0));
v___y_1386_ = v_a_1419_;
v___y_1387_ = v___x_1405_;
goto v___jp_1385_;
}
}
}
else
{
lean_object* v_putStr_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v___f_1332_);
lean_dec_ref(v_outputsFile_1329_);
v_putStr_1439_ = lean_ctor_get(v_out_1328_, 4);
lean_inc_ref(v_putStr_1439_);
lean_dec_ref(v_out_1328_);
v___x_1440_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10));
v___x_1441_ = lean_apply_2(v_putStr_1439_, v___x_1440_, lean_box(0));
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
return v_a_1442_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1909__overap_1457_; lean_object* v___x_1458_; 
v_a_1443_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1444_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1445_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1446_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1447_ = lean_unsigned_to_nat(89u);
v___x_1448_ = lean_unsigned_to_nat(4u);
v___x_1449_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1450_ = lean_io_error_to_string(v_a_1443_);
v___x_1451_ = lean_string_append(v___x_1449_, v___x_1450_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1453_ = lean_string_append(v___x_1451_, v___x_1452_);
v___x_1454_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
v___x_1456_ = l_mkPanicMessageWithDecl(v___x_1445_, v___x_1446_, v___x_1447_, v___x_1448_, v___x_1455_);
lean_dec_ref(v___x_1455_);
v___x_1909__overap_1457_ = l_panic___redArg(v___x_1444_, v___x_1456_);
v___x_1458_ = lean_apply_1(v___x_1909__overap_1457_, lean_box(0));
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1470_, lean_object* v_ws_1471_, lean_object* v_outputsRef_x3f_1472_, lean_object* v_out_1473_, lean_object* v_outputsFile_1474_, lean_object* v_isVerbose_1475_, lean_object* v_a_1476_){
_start:
{
uint8_t v_isVerbose_boxed_1477_; lean_object* v_res_1478_; 
v_isVerbose_boxed_1477_ = lean_unbox(v_isVerbose_1475_);
v_res_1478_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1470_, v_ws_1471_, v_outputsRef_x3f_1472_, v_out_1473_, v_outputsFile_1474_, v_isVerbose_boxed_1477_);
lean_dec(v_outputsRef_x3f_1472_);
lean_dec_ref(v_ws_1471_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1480_, lean_object* v_as_1481_, size_t v_i_1482_, size_t v_stop_1483_, lean_object* v_b_1484_){
_start:
{
lean_object* v_val_1487_; uint8_t v___x_1491_; 
v___x_1491_ = lean_usize_dec_eq(v_i_1482_, v_stop_1483_);
if (v___x_1491_ == 0)
{
lean_object* v_putStr_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_putStr_1492_ = lean_ctor_get(v_out_1480_, 4);
v___x_1493_ = lean_array_uget_borrowed(v_as_1481_, v_i_1482_);
v___x_1494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1495_ = lean_string_append(v___x_1494_, v___x_1493_);
v___x_1496_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
lean_inc_ref(v_putStr_1492_);
lean_inc_ref(v___x_1497_);
v___x_1498_ = lean_apply_2(v_putStr_1492_, v___x_1497_, lean_box(0));
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; 
lean_dec_ref(v___x_1497_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v_val_1487_ = v_a_1499_;
goto v___jp_1486_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1523_; 
v_a_1500_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1523_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1523_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1504_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1505_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1506_ = lean_unsigned_to_nat(89u);
v___x_1507_ = lean_unsigned_to_nat(4u);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1510_ = lean_io_error_to_string(v_a_1500_);
v___x_1511_ = lean_string_append(v___x_1509_, v___x_1510_);
lean_dec_ref(v___x_1510_);
v___x_1512_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1513_ = lean_string_append(v___x_1511_, v___x_1512_);
v___x_1514_ = l_String_quote(v___x_1497_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 3);
lean_ctor_set(v___x_1502_, 0, v___x_1514_);
v___x_1516_ = v___x_1502_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = l_Std_Format_defWidth;
v___x_1518_ = l_Std_Format_pretty(v___x_1516_, v___x_1517_, v___x_1508_, v___x_1508_);
v___x_1519_ = lean_string_append(v___x_1513_, v___x_1518_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = l_mkPanicMessageWithDecl(v___x_1504_, v___x_1505_, v___x_1506_, v___x_1507_, v___x_1519_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1520_);
v_val_1487_ = v___x_1521_;
goto v___jp_1486_;
}
}
}
}
else
{
lean_dec_ref(v_out_1480_);
return v_b_1484_;
}
v___jp_1486_:
{
size_t v___x_1488_; size_t v___x_1489_; 
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_add(v_i_1482_, v___x_1488_);
v_i_1482_ = v___x_1489_;
v_b_1484_ = v_val_1487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1524_, lean_object* v_as_1525_, lean_object* v_i_1526_, lean_object* v_stop_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_i_boxed_1530_; size_t v_stop_boxed_1531_; lean_object* v_res_1532_; 
v_i_boxed_1530_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_stop_boxed_1531_ = lean_unbox_usize(v_stop_1527_);
lean_dec(v_stop_1527_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1524_, v_as_1525_, v_i_boxed_1530_, v_stop_boxed_1531_, v_b_1528_);
lean_dec_ref(v_as_1525_);
return v_res_1532_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1540_ = l_String_quote(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = l_Std_Format_defWidth;
v___x_1545_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1546_ = l_Std_Format_pretty(v___x_1545_, v___x_1544_, v___x_1543_, v___x_1543_);
return v___x_1546_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1549_ = l_String_quote(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = l_Std_Format_defWidth;
v___x_1554_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1555_ = l_Std_Format_pretty(v___x_1554_, v___x_1553_, v___x_1552_, v___x_1552_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1556_, lean_object* v_out_1557_, lean_object* v_result_1558_){
_start:
{
uint8_t v___y_1561_; lean_object* v___y_1562_; lean_object* v_failures_1636_; lean_object* v_numJobs_1637_; uint8_t v___y_1639_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_failures_1636_ = lean_ctor_get(v_result_1558_, 0);
lean_inc_ref(v_failures_1636_);
v_numJobs_1637_ = lean_ctor_get(v_result_1558_, 1);
lean_inc(v_numJobs_1637_);
lean_dec_ref(v_result_1558_);
v___x_1672_ = lean_array_get_size(v_failures_1636_);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = lean_nat_dec_eq(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v_flush_1675_; lean_object* v_putStr_1676_; lean_object* v___y_1682_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec(v_numJobs_1637_);
v_flush_1675_ = lean_ctor_get(v_out_1557_, 0);
lean_inc_ref(v_flush_1675_);
v_putStr_1676_ = lean_ctor_get(v_out_1557_, 4);
v___x_1693_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1676_);
v___x_1694_ = lean_apply_2(v_putStr_1676_, v___x_1693_, lean_box(0));
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_dec_ref_known(v___x_1694_, 1);
goto v___jp_1683_;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1697_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1698_ = lean_unsigned_to_nat(89u);
v___x_1699_ = lean_unsigned_to_nat(4u);
v___x_1700_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1701_ = lean_io_error_to_string(v_a_1695_);
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1704_ = lean_string_append(v___x_1702_, v___x_1703_);
v___x_1705_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1706_ = lean_string_append(v___x_1704_, v___x_1705_);
v___x_1707_ = l_mkPanicMessageWithDecl(v___x_1696_, v___x_1697_, v___x_1698_, v___x_1699_, v___x_1706_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1707_);
goto v___jp_1683_;
}
v___jp_1677_:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_apply_1(v_flush_1675_, lean_box(0));
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
return v_a_1679_;
}
else
{
lean_object* v___x_1680_; 
lean_dec_ref_known(v___x_1678_, 1);
v___x_1680_ = lean_box(0);
return v___x_1680_;
}
}
v___jp_1681_:
{
goto v___jp_1677_;
}
v___jp_1683_:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_lt(v___x_1673_, v___x_1672_);
if (v___x_1684_ == 0)
{
lean_dec_ref(v_failures_1636_);
lean_dec_ref(v_out_1557_);
goto v___jp_1677_;
}
else
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_nat_dec_le(v___x_1672_, v___x_1672_);
if (v___x_1686_ == 0)
{
if (v___x_1684_ == 0)
{
lean_dec_ref(v_failures_1636_);
lean_dec_ref(v_out_1557_);
goto v___jp_1677_;
}
else
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = lean_usize_of_nat(v___x_1672_);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1557_, v_failures_1636_, v___x_1687_, v___x_1688_, v___x_1685_);
lean_dec_ref(v_failures_1636_);
v___y_1682_ = v___x_1689_;
goto v___jp_1681_;
}
}
else
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = lean_usize_of_nat(v___x_1672_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1557_, v_failures_1636_, v___x_1690_, v___x_1691_, v___x_1685_);
lean_dec_ref(v_failures_1636_);
v___y_1682_ = v___x_1692_;
goto v___jp_1681_;
}
}
}
}
else
{
uint8_t v___x_1709_; 
lean_dec_ref(v_failures_1636_);
v___x_1709_ = l_Lake_BuildConfig_showProgress(v_cfg_1556_);
if (v___x_1709_ == 0)
{
v___y_1639_ = v___x_1709_;
goto v___jp_1638_;
}
else
{
uint8_t v_showSuccess_1710_; 
v_showSuccess_1710_ = lean_ctor_get_uint8(v_cfg_1556_, sizeof(void*)*3 + 4);
v___y_1639_ = v_showSuccess_1710_;
goto v___jp_1638_;
}
}
v___jp_1560_:
{
uint8_t v_noBuild_1563_; 
v_noBuild_1563_ = lean_ctor_get_uint8(v_cfg_1556_, sizeof(void*)*3 + 2);
if (v_noBuild_1563_ == 0)
{
lean_object* v_putStr_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_putStr_1564_ = lean_ctor_get(v_out_1557_, 4);
lean_inc_ref(v_putStr_1564_);
lean_dec_ref(v_out_1557_);
v___x_1565_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1566_ = lean_string_append(v___x_1565_, v___y_1562_);
lean_dec_ref(v___y_1562_);
v___x_1567_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1568_ = lean_string_append(v___x_1566_, v___x_1567_);
lean_inc_ref(v___x_1568_);
v___x_1569_ = lean_apply_2(v_putStr_1564_, v___x_1568_, lean_box(0));
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; 
lean_dec_ref(v___x_1568_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
return v_a_1570_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1599_; 
v_a_1571_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1573_ = v___x_1569_;
v_isShared_1574_ = v_isSharedCheck_1599_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1569_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1599_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1575_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1576_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1577_ = lean_unsigned_to_nat(89u);
v___x_1578_ = lean_unsigned_to_nat(4u);
v___x_1579_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1582_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1581_, v___y_1561_);
v___x_1583_ = lean_string_append(v___x_1579_, v___x_1582_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
v___x_1586_ = lean_io_error_to_string(v_a_1571_);
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
v___x_1590_ = l_String_quote(v___x_1568_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 3);
lean_ctor_set(v___x_1573_, 0, v___x_1590_);
v___x_1592_ = v___x_1573_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1593_ = l_Std_Format_defWidth;
v___x_1594_ = l_Std_Format_pretty(v___x_1592_, v___x_1593_, v___x_1580_, v___x_1580_);
v___x_1595_ = lean_string_append(v___x_1589_, v___x_1594_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = l_mkPanicMessageWithDecl(v___x_1575_, v___x_1576_, v___x_1577_, v___x_1578_, v___x_1595_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1596_);
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_putStr_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_putStr_1600_ = lean_ctor_get(v_out_1557_, 4);
lean_inc_ref(v_putStr_1600_);
lean_dec_ref(v_out_1557_);
v___x_1601_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1602_ = lean_string_append(v___x_1601_, v___y_1562_);
lean_dec_ref(v___y_1562_);
v___x_1603_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
lean_inc_ref(v___x_1604_);
v___x_1605_ = lean_apply_2(v_putStr_1600_, v___x_1604_, lean_box(0));
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; 
lean_dec_ref(v___x_1604_);
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
return v_a_1606_;
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1635_; 
v_a_1607_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1609_ = v___x_1605_;
v_isShared_1610_ = v_isSharedCheck_1635_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1605_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1635_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1611_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1612_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1613_ = lean_unsigned_to_nat(89u);
v___x_1614_ = lean_unsigned_to_nat(4u);
v___x_1615_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1618_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1617_, v_noBuild_1563_);
v___x_1619_ = lean_string_append(v___x_1615_, v___x_1618_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
v___x_1622_ = lean_io_error_to_string(v_a_1607_);
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
v___x_1626_ = l_String_quote(v___x_1604_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 3);
lean_ctor_set(v___x_1609_, 0, v___x_1626_);
v___x_1628_ = v___x_1609_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1629_ = l_Std_Format_defWidth;
v___x_1630_ = l_Std_Format_pretty(v___x_1628_, v___x_1629_, v___x_1616_, v___x_1616_);
v___x_1631_ = lean_string_append(v___x_1625_, v___x_1630_);
lean_dec_ref(v___x_1630_);
v___x_1632_ = l_mkPanicMessageWithDecl(v___x_1611_, v___x_1612_, v___x_1613_, v___x_1614_, v___x_1631_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1632_);
return v___x_1633_;
}
}
}
}
}
v___jp_1638_:
{
if (v___y_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_dec(v_numJobs_1637_);
lean_dec_ref(v_out_1557_);
v___x_1640_ = lean_box(0);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_nat_dec_eq(v_numJobs_1637_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_dec_eq(v_numJobs_1637_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = l_Nat_reprFast(v_numJobs_1637_);
v___x_1646_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
v___y_1561_ = v___y_1639_;
v___y_1562_ = v___x_1647_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1648_; 
lean_dec(v_numJobs_1637_);
v___x_1648_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1561_ = v___y_1639_;
v___y_1562_ = v___x_1648_;
goto v___jp_1560_;
}
}
else
{
lean_object* v_putStr_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_numJobs_1637_);
v_putStr_1649_ = lean_ctor_get(v_out_1557_, 4);
lean_inc_ref(v_putStr_1649_);
lean_dec_ref(v_out_1557_);
v___x_1650_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1651_ = lean_apply_2(v_putStr_1649_, v___x_1650_, lean_box(0));
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
return v_a_1652_;
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_a_1653_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1654_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1655_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1656_ = lean_unsigned_to_nat(89u);
v___x_1657_ = lean_unsigned_to_nat(4u);
v___x_1658_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1659_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1659_, v___x_1642_);
v___x_1661_ = lean_string_append(v___x_1658_, v___x_1660_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1663_ = lean_string_append(v___x_1661_, v___x_1662_);
v___x_1664_ = lean_io_error_to_string(v_a_1653_);
v___x_1665_ = lean_string_append(v___x_1663_, v___x_1664_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1667_ = lean_string_append(v___x_1665_, v___x_1666_);
v___x_1668_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1669_ = lean_string_append(v___x_1667_, v___x_1668_);
v___x_1670_ = l_mkPanicMessageWithDecl(v___x_1654_, v___x_1655_, v___x_1656_, v___x_1657_, v___x_1669_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1670_);
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1711_, lean_object* v_out_1712_, lean_object* v_result_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1711_, v_out_1712_, v_result_1713_);
lean_dec_ref(v_cfg_1711_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1716_){
_start:
{
lean_object* v_toMonitorResult_1717_; 
v_toMonitorResult_1717_ = lean_ctor_get(v_self_1716_, 0);
lean_inc_ref(v_toMonitorResult_1717_);
return v_toMonitorResult_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1718_);
lean_dec_ref(v_self_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1721_){
_start:
{
lean_object* v___f_1722_; 
v___f_1722_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1722_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1723_){
_start:
{
lean_object* v_out_1724_; 
v_out_1724_ = lean_ctor_get(v_self_1723_, 1);
if (lean_obj_tag(v_out_1724_) == 0)
{
uint8_t v___x_1725_; 
v___x_1725_ = 0;
return v___x_1725_;
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = 1;
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1727_){
_start:
{
uint8_t v_res_1728_; lean_object* v_r_1729_; 
v_res_1728_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1727_);
lean_dec_ref(v_self_1727_);
v_r_1729_ = lean_box(v_res_1728_);
return v_r_1729_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1730_, lean_object* v_self_1731_){
_start:
{
lean_object* v_out_1732_; 
v_out_1732_ = lean_ctor_get(v_self_1731_, 1);
if (lean_obj_tag(v_out_1732_) == 0)
{
uint8_t v___x_1733_; 
v___x_1733_ = 0;
return v___x_1733_;
}
else
{
uint8_t v___x_1734_; 
v___x_1734_ = 1;
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_self_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1735_, v_self_1736_);
lean_dec_ref(v_self_1736_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1747_, lean_object* v_job_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_failures_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
lean_inc_ref(v_job_1748_);
v___x_1750_ = l_Lake_Job_toOpaque___redArg(v_job_1748_);
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = lean_array_push(v___x_1752_, v___x_1750_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1756_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1757_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1747_, v___x_1753_, v___x_1755_, v___x_1756_);
v_failures_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_ref(v_failures_1758_);
v___x_1759_ = lean_array_get_size(v_failures_1758_);
lean_dec_ref(v_failures_1758_);
v___x_1760_ = lean_nat_dec_eq(v___x_1759_, v___x_1754_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec_ref(v_job_1748_);
v___x_1761_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1757_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
return v___x_1762_;
}
else
{
lean_object* v_task_1763_; lean_object* v___x_1764_; 
v_task_1763_ = lean_ctor_get(v_job_1748_, 0);
lean_inc_ref(v_task_1763_);
lean_dec_ref(v_job_1748_);
v___x_1764_ = lean_io_wait(v_task_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1773_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1764_, 1);
lean_dec(v_unused_1774_);
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1769_);
lean_ctor_set(v___x_1767_, 0, v___x_1757_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1782_; 
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; lean_object* v_unused_1784_; 
v_unused_1783_ = lean_ctor_get(v___x_1764_, 1);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v___x_1764_, 0);
lean_dec(v_unused_1784_);
v___x_1776_ = v___x_1764_;
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v___x_1764_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 0);
lean_ctor_set(v___x_1776_, 1, v___x_1778_);
lean_ctor_set(v___x_1776_, 0, v___x_1757_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1785_, lean_object* v_job_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1785_, v_job_1786_);
lean_dec_ref(v_ctx_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1789_, lean_object* v_ctx_1790_, lean_object* v_job_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1790_, v_job_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_ctx_1795_, lean_object* v_job_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1794_, v_ctx_1795_, v_job_1796_);
lean_dec_ref(v_ctx_1795_);
return v_res_1798_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_unsigned_to_nat(16u);
v___x_1803_ = lean_mk_array(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* v_ws_1807_, lean_object* v_cfg_1808_, lean_object* v_jobs_1809_){
_start:
{
lean_object* v_val_1812_; lean_object* v_outputsFile_x3f_1824_; 
v_outputsFile_x3f_1824_ = lean_ctor_get(v_cfg_1808_, 1);
lean_inc(v_outputsFile_x3f_1824_);
if (lean_obj_tag(v_outputsFile_x3f_1824_) == 0)
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_box(0);
v_val_1812_ = v___x_1825_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1834_; 
v_isSharedCheck_1834_ = !lean_is_exclusive(v_outputsFile_x3f_1824_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v_outputsFile_x3f_1824_, 0);
lean_dec(v_unused_1835_);
v___x_1827_ = v_outputsFile_x3f_1824_;
v_isShared_1828_ = v_isSharedCheck_1834_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v_outputsFile_x3f_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1834_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1829_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2);
v___x_1830_ = lean_st_mk_ref(v___x_1829_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1830_);
v___x_1832_ = v___x_1827_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
v_val_1812_ = v___x_1832_;
goto v___jp_1811_;
}
}
}
v___jp_1811_:
{
lean_object* v_lakeEnv_1813_; lean_object* v___x_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; uint64_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_lakeEnv_1813_ = lean_ctor_get(v_ws_1807_, 0);
v___x_1814_ = l_Lake_Env_leanGithash(v_lakeEnv_1813_);
v___x_1815_ = l_Lake_Hash_nil;
v___x_1816_ = lean_string_hash(v___x_1814_);
v___x_1817_ = lean_uint64_mix_hash(v___x_1815_, v___x_1816_);
v___x_1818_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_1819_ = lean_string_append(v___x_1818_, v___x_1814_);
lean_dec_ref(v___x_1814_);
v___x_1820_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
v___x_1821_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_1822_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1822_, 0, v___x_1819_);
lean_ctor_set(v___x_1822_, 1, v___x_1820_);
lean_ctor_set(v___x_1822_, 2, v___x_1821_);
lean_ctor_set_uint64(v___x_1822_, sizeof(void*)*3, v___x_1817_);
v___x_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1823_, 0, v_cfg_1808_);
lean_ctor_set(v___x_1823_, 1, v_ws_1807_);
lean_ctor_set(v___x_1823_, 2, v___x_1822_);
lean_ctor_set(v___x_1823_, 3, v_jobs_1809_);
lean_ctor_set(v___x_1823_, 4, v_val_1812_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(lean_object* v_ws_1836_, lean_object* v_cfg_1837_, lean_object* v_jobs_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_1836_, v_cfg_1837_, v_jobs_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_log_1849_; uint8_t v_action_1850_; uint8_t v_wantsRebuild_1851_; lean_object* v_trace_1852_; lean_object* v_buildTime_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1882_; 
v_log_1849_ = lean_ctor_get(v___y_1847_, 0);
v_action_1850_ = lean_ctor_get_uint8(v___y_1847_, sizeof(void*)*3);
v_wantsRebuild_1851_ = lean_ctor_get_uint8(v___y_1847_, sizeof(void*)*3 + 1);
v_trace_1852_ = lean_ctor_get(v___y_1847_, 1);
v_buildTime_1853_ = lean_ctor_get(v___y_1847_, 2);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___y_1847_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1855_ = v___y_1847_;
v_isShared_1856_ = v_isSharedCheck_1882_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_buildTime_1853_);
lean_inc(v_trace_1852_);
lean_inc(v_log_1849_);
lean_dec(v___y_1847_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1882_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_apply_7(v_build_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v_log_1849_, lean_box(0));
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1869_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_a_1859_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1869_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1869_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_a_1859_);
v___x_1864_ = v___x_1855_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1859_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_trace_1852_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_buildTime_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, sizeof(void*)*3, v_action_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, sizeof(void*)*3 + 1, v_wantsRebuild_1851_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1858_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1881_; 
v_a_1870_ = lean_ctor_get(v___x_1857_, 0);
v_a_1871_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1873_ = v___x_1857_;
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_inc(v_a_1870_);
lean_dec(v___x_1857_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_a_1871_);
v___x_1876_ = v___x_1855_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1871_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_trace_1852_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_buildTime_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*3, v_action_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*3 + 1, v_wantsRebuild_1851_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1870_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_1893_, lean_object* v_build_1894_, lean_object* v_caption_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1897_ = lean_box(1);
v___x_1898_ = lean_st_mk_ref(v___x_1897_);
v___f_1899_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1899_, 0, v_build_1894_);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_box(0);
v___x_1904_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_1905_ = l_Lake_Job_async___redArg(v___x_1900_, v___f_1899_, v___x_1901_, v_caption_1895_, v___x_1904_, v___x_1903_, v___x_1902_, v___x_1898_, v_bctx_1893_);
v___x_1906_ = lean_st_ref_get(v___x_1898_);
lean_dec(v___x_1898_);
lean_dec(v___x_1906_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_1907_, lean_object* v_build_1908_, lean_object* v_caption_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1907_, v_build_1908_, v_caption_1909_);
lean_dec_ref(v_bctx_1907_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_1912_, lean_object* v_bctx_1913_, lean_object* v_build_1914_, lean_object* v_caption_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1913_, v_build_1914_, v_caption_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_bctx_1919_, lean_object* v_build_1920_, lean_object* v_caption_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_1918_, v_bctx_1919_, v_build_1920_, v_caption_1921_);
lean_dec_ref(v_bctx_1919_);
return v_res_1923_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1924_) == 0)
{
if (lean_obj_tag(v_x_1925_) == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = 1;
return v___x_1926_;
}
else
{
uint8_t v___x_1927_; 
v___x_1927_ = 0;
return v___x_1927_;
}
}
else
{
if (lean_obj_tag(v_x_1925_) == 0)
{
uint8_t v___x_1928_; 
v___x_1928_ = 0;
return v___x_1928_;
}
else
{
lean_object* v_val_1929_; uint8_t v___x_1930_; 
v_val_1929_ = lean_ctor_get(v_x_1924_, 0);
v___x_1930_ = lean_unbox(v_val_1929_);
if (v___x_1930_ == 0)
{
lean_object* v_val_1931_; uint8_t v___x_1932_; 
v_val_1931_ = lean_ctor_get(v_x_1925_, 0);
v___x_1932_ = lean_unbox(v_val_1931_);
if (v___x_1932_ == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = 1;
return v___x_1933_;
}
else
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_unbox(v_val_1929_);
return v___x_1934_;
}
}
else
{
lean_object* v_val_1935_; uint8_t v___x_1936_; 
v_val_1935_ = lean_ctor_get(v_x_1925_, 0);
v___x_1936_ = lean_unbox(v_val_1935_);
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v_x_1937_, lean_object* v_x_1938_){
_start:
{
uint8_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_1937_, v_x_1938_);
lean_dec(v_x_1938_);
lean_dec(v_x_1937_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_1941_, uint8_t v___x_1942_, uint8_t v___x_1943_, lean_object* v_as_1944_, size_t v_i_1945_, size_t v_stop_1946_, lean_object* v_b_1947_){
_start:
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_usize_dec_eq(v_i_1945_, v_stop_1946_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; 
v___x_1950_ = lean_array_uget_borrowed(v_as_1944_, v_i_1945_);
lean_inc_ref(v___x_1941_);
v___x_1951_ = l_Lake_logToStream(v___x_1950_, v___x_1941_, v___x_1942_, v___x_1943_);
v___x_1952_ = ((size_t)1ULL);
v___x_1953_ = lean_usize_add(v_i_1945_, v___x_1952_);
v_i_1945_ = v___x_1953_;
v_b_1947_ = v___x_1951_;
goto _start;
}
else
{
lean_dec_ref(v___x_1941_);
return v_b_1947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_1955_, lean_object* v___x_1956_, lean_object* v___x_1957_, lean_object* v_as_1958_, lean_object* v_i_1959_, lean_object* v_stop_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v___x_1089__boxed_1963_; uint8_t v___x_1090__boxed_1964_; size_t v_i_boxed_1965_; size_t v_stop_boxed_1966_; lean_object* v_res_1967_; 
v___x_1089__boxed_1963_ = lean_unbox(v___x_1956_);
v___x_1090__boxed_1964_ = lean_unbox(v___x_1957_);
v_i_boxed_1965_ = lean_unbox_usize(v_i_1959_);
lean_dec(v_i_1959_);
v_stop_boxed_1966_ = lean_unbox_usize(v_stop_1960_);
lean_dec(v_stop_1960_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1955_, v___x_1089__boxed_1963_, v___x_1090__boxed_1964_, v_as_1958_, v_i_boxed_1965_, v_stop_boxed_1966_, v_b_1961_);
lean_dec_ref(v_as_1958_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_1968_, uint8_t v___x_1969_, uint8_t v___x_1970_, lean_object* v_ws_1971_, lean_object* v_outputsRef_x3f_1972_, lean_object* v_out_1973_, lean_object* v_outputsFile_1974_, uint8_t v_isVerbose_1975_){
_start:
{
lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_2025_; lean_object* v___y_2026_; uint8_t v___x_2091_; 
v___x_2091_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1971_);
if (v___x_2091_ == 0)
{
lean_object* v_packages_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_baseName_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_packages_2092_ = lean_ctor_get(v_ws_1971_, 4);
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_array_fget_borrowed(v_packages_2092_, v___x_2093_);
v_baseName_2095_ = lean_ctor_get(v___x_2094_, 1);
lean_inc(v_baseName_2095_);
v___x_2096_ = l_Lean_Name_toString(v_baseName_2095_, v___x_2091_);
v___x_2097_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14));
v___x_2098_ = lean_string_append(v___x_2096_, v___x_2097_);
v___x_2099_ = 2;
v___x_2100_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*1, v___x_2099_);
lean_inc_ref(v___x_1968_);
v___x_2101_ = l_Lake_logToStream(v___x_2100_, v___x_1968_, v___x_1969_, v___x_1970_);
lean_dec_ref_known(v___x_2100_, 1);
goto v___jp_2038_;
}
else
{
goto v___jp_2038_;
}
v___jp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1980_ = lean_array_get_size(v___y_1979_);
v___x_1981_ = lean_box(0);
v___x_1982_ = lean_nat_dec_lt(v___y_1978_, v___x_1980_);
lean_dec(v___y_1978_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v___y_1979_);
lean_dec_ref(v___x_1968_);
return v___x_1981_;
}
else
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_nat_dec_le(v___x_1980_, v___x_1980_);
if (v___x_1983_ == 0)
{
if (v___x_1982_ == 0)
{
lean_dec_ref(v___y_1979_);
lean_dec_ref(v___x_1968_);
return v___x_1981_;
}
else
{
size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = lean_usize_of_nat(v___x_1980_);
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1968_, v___x_1969_, v___x_1970_, v___y_1979_, v___x_1984_, v___x_1985_, v___x_1981_);
lean_dec_ref(v___y_1979_);
return v___x_1986_;
}
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = lean_usize_of_nat(v___x_1980_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1968_, v___x_1969_, v___x_1970_, v___y_1979_, v___x_1987_, v___x_1988_, v___x_1981_);
lean_dec_ref(v___y_1979_);
return v___x_1989_;
}
}
}
v___jp_1990_:
{
if (v___y_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v_out_1973_);
lean_dec_ref(v___x_1968_);
v___x_1994_ = lean_box(0);
return v___x_1994_;
}
else
{
lean_object* v_putStr_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_putStr_1995_ = lean_ctor_get(v_out_1973_, 4);
lean_inc_ref(v_putStr_1995_);
lean_dec_ref(v_out_1973_);
v___x_1996_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
v___x_1997_ = lean_apply_2(v_putStr_1995_, v___x_1996_, lean_box(0));
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_dec_ref_known(v___x_1997_, 1);
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1991_;
goto v___jp_1977_;
}
else
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2000_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2001_ = lean_unsigned_to_nat(89u);
v___x_2002_ = lean_unsigned_to_nat(4u);
v___x_2003_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2004_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_2005_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc_n(v___y_1992_, 3);
v___x_2006_ = l_Lean_Name_num___override(v___x_2005_, v___y_1992_);
v___x_2007_ = l_Lean_Name_str___override(v___x_2006_, v___x_2004_);
v___x_2008_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_2009_ = l_Lean_Name_str___override(v___x_2007_, v___x_2008_);
v___x_2010_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2009_, v___y_1993_);
v___x_2011_ = lean_string_append(v___x_2003_, v___x_2010_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2013_ = lean_string_append(v___x_2011_, v___x_2012_);
v___x_2014_ = lean_io_error_to_string(v_a_1998_);
v___x_2015_ = lean_string_append(v___x_2013_, v___x_2014_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2017_ = lean_string_append(v___x_2015_, v___x_2016_);
v___x_2018_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2);
v___x_2019_ = l_Std_Format_defWidth;
v___x_2020_ = l_Std_Format_pretty(v___x_2018_, v___x_2019_, v___y_1992_, v___y_1992_);
v___x_2021_ = lean_string_append(v___x_2017_, v___x_2020_);
lean_dec_ref(v___x_2020_);
v___x_2022_ = l_mkPanicMessageWithDecl(v___x_1999_, v___x_2000_, v___x_2001_, v___x_2002_, v___x_2021_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2022_);
v___y_1978_ = v___y_1992_;
v___y_1979_ = v___y_1991_;
goto v___jp_1977_;
}
}
}
v___jp_2024_:
{
if (v_isVerbose_1975_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___x_1968_);
v___x_2027_ = lean_box(0);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = lean_array_get_size(v___y_2025_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_nat_dec_lt(v___y_2026_, v___x_2028_);
lean_dec(v___y_2026_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___x_1968_);
return v___x_2029_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_nat_dec_le(v___x_2028_, v___x_2028_);
if (v___x_2031_ == 0)
{
if (v___x_2030_ == 0)
{
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___x_1968_);
return v___x_2029_;
}
else
{
size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = lean_usize_of_nat(v___x_2028_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1968_, v___x_1969_, v___x_1970_, v___y_2025_, v___x_2032_, v___x_2033_, v___x_2029_);
lean_dec_ref(v___y_2025_);
return v___x_2034_;
}
}
else
{
size_t v___x_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = lean_usize_of_nat(v___x_2028_);
v___x_2037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1968_, v___x_1969_, v___x_1970_, v___y_2025_, v___x_2035_, v___x_2036_, v___x_2029_);
lean_dec_ref(v___y_2025_);
return v___x_2037_;
}
}
}
}
v___jp_2038_:
{
if (lean_obj_tag(v_outputsRef_x3f_1972_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2040_; lean_object* v_packages_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_config_2044_; lean_object* v_toLeanConfig_2045_; lean_object* v_platformIndependent_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_val_2039_ = lean_ctor_get(v_outputsRef_x3f_1972_, 0);
v___x_2040_ = lean_st_ref_get(v_val_2039_);
v_packages_2041_ = lean_ctor_get(v_ws_1971_, 4);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_array_fget_borrowed(v_packages_2041_, v___x_2042_);
v_config_2044_ = lean_ctor_get(v___x_2043_, 6);
v_toLeanConfig_2045_ = lean_ctor_get(v_config_2044_, 1);
v_platformIndependent_2046_ = lean_ctor_get(v_toLeanConfig_2045_, 10);
v___x_2047_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_2048_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_2046_, v___x_2047_);
v___x_2049_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
v___x_2050_ = l_Lake_CacheMap_writeFile(v_outputsFile_1974_, v___x_2040_, v___x_2048_, v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; uint8_t v___x_2054_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 2);
v___x_2052_ = lean_array_get_size(v_a_2051_);
v___x_2053_ = lean_nat_dec_eq(v___x_2052_, v___x_2042_);
v___x_2054_ = lean_bool_not(v___x_2053_);
if (v___x_2054_ == 0)
{
v___y_1991_ = v_a_2051_;
v___y_1992_ = v___x_2042_;
v___y_1993_ = v___x_2054_;
goto v___jp_1990_;
}
else
{
v___y_1991_ = v_a_2051_;
v___y_1992_ = v___x_2042_;
v___y_1993_ = v_isVerbose_1975_;
goto v___jp_1990_;
}
}
else
{
lean_object* v_a_2055_; lean_object* v_putStr_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2055_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2050_, 2);
v_putStr_2056_ = lean_ctor_get(v_out_1973_, 4);
lean_inc_ref(v_putStr_2056_);
lean_dec_ref(v_out_1973_);
v___x_2057_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6));
v___x_2058_ = lean_apply_2(v_putStr_2056_, v___x_2057_, lean_box(0));
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_dec_ref_known(v___x_2058_, 1);
v___y_2025_ = v_a_2055_;
v___y_2026_ = v___x_2042_;
goto v___jp_2024_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2061_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2062_ = lean_unsigned_to_nat(89u);
v___x_2063_ = lean_unsigned_to_nat(4u);
v___x_2064_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2065_ = lean_io_error_to_string(v_a_2059_);
v___x_2066_ = lean_string_append(v___x_2064_, v___x_2065_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2068_ = lean_string_append(v___x_2066_, v___x_2067_);
v___x_2069_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_2070_ = lean_string_append(v___x_2068_, v___x_2069_);
v___x_2071_ = l_mkPanicMessageWithDecl(v___x_2060_, v___x_2061_, v___x_2062_, v___x_2063_, v___x_2070_);
lean_dec_ref(v___x_2070_);
v___x_2072_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2071_);
v___y_2025_ = v_a_2055_;
v___y_2026_ = v___x_2042_;
goto v___jp_2024_;
}
}
}
else
{
lean_object* v_putStr_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec_ref(v_outputsFile_1974_);
lean_dec_ref(v___x_1968_);
v_putStr_2073_ = lean_ctor_get(v_out_1973_, 4);
lean_inc_ref(v_putStr_2073_);
lean_dec_ref(v_out_1973_);
v___x_2074_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10));
v___x_2075_ = lean_apply_2(v_putStr_2073_, v___x_2074_, lean_box(0));
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
return v_a_2076_;
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2077_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2078_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2079_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2080_ = lean_unsigned_to_nat(89u);
v___x_2081_ = lean_unsigned_to_nat(4u);
v___x_2082_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2083_ = lean_io_error_to_string(v_a_2077_);
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
v___x_2087_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
v___x_2089_ = l_mkPanicMessageWithDecl(v___x_2078_, v___x_2079_, v___x_2080_, v___x_2081_, v___x_2088_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2089_);
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2102_, lean_object* v___x_2103_, lean_object* v___x_2104_, lean_object* v_ws_2105_, lean_object* v_outputsRef_x3f_2106_, lean_object* v_out_2107_, lean_object* v_outputsFile_2108_, lean_object* v_isVerbose_2109_, lean_object* v_a_2110_){
_start:
{
uint8_t v___x_1245__boxed_2111_; uint8_t v___x_1246__boxed_2112_; uint8_t v_isVerbose_boxed_2113_; lean_object* v_res_2114_; 
v___x_1245__boxed_2111_ = lean_unbox(v___x_2103_);
v___x_1246__boxed_2112_ = lean_unbox(v___x_2104_);
v_isVerbose_boxed_2113_ = lean_unbox(v_isVerbose_2109_);
v_res_2114_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2102_, v___x_1245__boxed_2111_, v___x_1246__boxed_2112_, v_ws_2105_, v_outputsRef_x3f_2106_, v_out_2107_, v_outputsFile_2108_, v_isVerbose_boxed_2113_);
lean_dec(v_outputsRef_x3f_2106_);
lean_dec_ref(v_ws_2105_);
return v_res_2114_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = 3;
v___x_2116_ = lean_uint32_to_uint8(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2117_, lean_object* v_bctx_2118_, lean_object* v_mctx_2119_, lean_object* v_result_2120_){
_start:
{
lean_object* v___y_2123_; lean_object* v_out_2126_; uint8_t v_outLv_2127_; uint8_t v_useAnsi_2128_; lean_object* v_toMonitorResult_2129_; lean_object* v_out_2130_; lean_object* v___x_2131_; uint8_t v_noBuild_2132_; uint8_t v_verbosity_2133_; lean_object* v_outputsFile_x3f_2134_; 
v_out_2126_ = lean_ctor_get(v_mctx_2119_, 1);
lean_inc_ref_n(v_out_2126_, 2);
v_outLv_2127_ = lean_ctor_get_uint8(v_mctx_2119_, sizeof(void*)*3);
v_useAnsi_2128_ = lean_ctor_get_uint8(v_mctx_2119_, sizeof(void*)*3 + 4);
lean_dec_ref(v_mctx_2119_);
v_toMonitorResult_2129_ = lean_ctor_get(v_result_2120_, 0);
lean_inc_ref_n(v_toMonitorResult_2129_, 2);
v_out_2130_ = lean_ctor_get(v_result_2120_, 1);
lean_inc_ref(v_out_2130_);
lean_dec_ref(v_result_2120_);
v___x_2131_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2117_, v_out_2126_, v_toMonitorResult_2129_);
v_noBuild_2132_ = lean_ctor_get_uint8(v_cfg_2117_, sizeof(void*)*3 + 2);
v_verbosity_2133_ = lean_ctor_get_uint8(v_cfg_2117_, sizeof(void*)*3 + 3);
v_outputsFile_x3f_2134_ = lean_ctor_get(v_cfg_2117_, 1);
lean_inc(v_outputsFile_x3f_2134_);
lean_dec_ref(v_cfg_2117_);
if (lean_obj_tag(v_outputsFile_x3f_2134_) == 1)
{
lean_object* v_val_2149_; lean_object* v_toContext_2150_; lean_object* v_outputsRef_x3f_2151_; uint8_t v___y_2153_; 
v_val_2149_ = lean_ctor_get(v_outputsFile_x3f_2134_, 0);
lean_inc(v_val_2149_);
lean_dec_ref_known(v_outputsFile_x3f_2134_, 1);
v_toContext_2150_ = lean_ctor_get(v_bctx_2118_, 1);
v_outputsRef_x3f_2151_ = lean_ctor_get(v_bctx_2118_, 4);
if (v_verbosity_2133_ == 2)
{
uint8_t v___x_2155_; 
v___x_2155_ = 1;
v___y_2153_ = v___x_2155_;
goto v___jp_2152_;
}
else
{
uint8_t v___x_2156_; 
v___x_2156_ = 0;
v___y_2153_ = v___x_2156_;
goto v___jp_2152_;
}
v___jp_2152_:
{
lean_object* v___x_2154_; 
lean_inc_ref(v_out_2126_);
v___x_2154_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2126_, v_outLv_2127_, v_useAnsi_2128_, v_toContext_2150_, v_outputsRef_x3f_2151_, v_out_2126_, v_val_2149_, v___y_2153_);
goto v___jp_2135_;
}
}
else
{
lean_dec(v_outputsFile_x3f_2134_);
lean_dec_ref(v_out_2126_);
goto v___jp_2135_;
}
v___jp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_mk_io_user_error(v___y_2123_);
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
v___jp_2135_:
{
if (lean_obj_tag(v_out_2130_) == 0)
{
if (v_noBuild_2132_ == 0)
{
lean_object* v_a_2136_; 
lean_dec_ref(v_toMonitorResult_2129_);
v_a_2136_ = lean_ctor_get(v_out_2130_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v_out_2130_, 1);
v___y_2123_ = v_a_2136_;
goto v___jp_2122_;
}
else
{
uint8_t v_wantsRebuild_2137_; 
v_wantsRebuild_2137_ = lean_ctor_get_uint8(v_toMonitorResult_2129_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2129_);
if (v_wantsRebuild_2137_ == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v_out_2130_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v_out_2130_, 1);
v___y_2123_ = v_a_2138_;
goto v___jp_2122_;
}
else
{
uint8_t v___x_2139_; lean_object* v___x_2140_; 
lean_dec_ref_known(v_out_2130_, 1);
v___x_2139_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2140_ = lean_io_exit(v___x_2139_);
return v___x_2140_;
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_toMonitorResult_2129_);
v_a_2141_ = lean_ctor_get(v_out_2130_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_out_2130_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v_out_2130_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v_out_2130_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 0);
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2157_, lean_object* v_bctx_2158_, lean_object* v_mctx_2159_, lean_object* v_result_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2157_, v_bctx_2158_, v_mctx_2159_, v_result_2160_);
lean_dec_ref(v_bctx_2158_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2163_, lean_object* v_cfg_2164_, lean_object* v_bctx_2165_, lean_object* v_mctx_2166_, lean_object* v_result_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2164_, v_bctx_2165_, v_mctx_2166_, v_result_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_cfg_2171_, lean_object* v_bctx_2172_, lean_object* v_mctx_2173_, lean_object* v_result_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2170_, v_cfg_2171_, v_bctx_2172_, v_mctx_2173_, v_result_2174_);
lean_dec_ref(v_bctx_2172_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2177_, lean_object* v_build_2178_, lean_object* v_cfg_2179_, lean_object* v_caption_2180_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2182_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2183_ = lean_st_mk_ref(v___x_2182_);
lean_inc(v___x_2183_);
v___x_2184_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2179_, v___x_2183_);
lean_inc_ref(v_cfg_2179_);
v___x_2185_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2177_, v_cfg_2179_, v___x_2183_);
v___x_2186_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2185_, v_build_2178_, v_caption_2180_);
v___x_2187_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2184_, v___x_2186_);
v___x_2188_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2179_, v___x_2185_, v___x_2184_, v___x_2187_);
lean_dec_ref(v___x_2185_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2189_, lean_object* v_build_2190_, lean_object* v_cfg_2191_, lean_object* v_caption_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2189_, v_build_2190_, v_cfg_2191_, v_caption_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2195_, lean_object* v_ws_2196_, lean_object* v_build_2197_, lean_object* v_cfg_2198_, lean_object* v_caption_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2196_, v_build_2197_, v_cfg_2198_, v_caption_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2202_, lean_object* v_ws_2203_, lean_object* v_build_2204_, lean_object* v_cfg_2205_, lean_object* v_caption_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2202_, v_ws_2203_, v_build_2204_, v_cfg_2205_, v_caption_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2212_, lean_object* v_job_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v_out_2216_; 
v___x_2215_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2212_, v_job_2213_);
v_out_2216_ = lean_ctor_get(v___x_2215_, 1);
lean_inc_ref(v_out_2216_);
if (lean_obj_tag(v_out_2216_) == 0)
{
lean_object* v_toMonitorResult_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2232_; 
v_toMonitorResult_2217_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v___x_2215_, 1);
lean_dec(v_unused_2233_);
v___x_2219_ = v___x_2215_;
v_isShared_2220_ = v_isSharedCheck_2232_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_toMonitorResult_2217_);
lean_dec(v___x_2215_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2232_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2231_; 
v_a_2221_ = lean_ctor_get(v_out_2216_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_out_2216_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2223_ = v_out_2216_;
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v_out_2216_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2231_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2226_);
v___x_2228_ = v___x_2219_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_toMonitorResult_2217_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2257_; 
v_a_2234_ = lean_ctor_get(v_out_2216_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_out_2216_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2236_ = v_out_2216_;
v_isShared_2237_ = v_isSharedCheck_2257_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v_out_2216_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2257_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v_toMonitorResult_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2255_; 
v_toMonitorResult_2238_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2215_, 1);
lean_dec(v_unused_2256_);
v___x_2240_ = v___x_2215_;
v_isShared_2241_ = v_isSharedCheck_2255_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_toMonitorResult_2238_);
lean_dec(v___x_2215_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2255_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_task_2242_; lean_object* v___x_2243_; 
v_task_2242_ = lean_ctor_get(v_a_2234_, 0);
lean_inc_ref(v_task_2242_);
lean_dec(v_a_2234_);
v___x_2243_ = lean_io_wait(v_task_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 2);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_a_2244_);
v___x_2246_ = v___x_2236_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2246_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 1, v___x_2246_);
v___x_2248_ = v___x_2240_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_toMonitorResult_2238_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_dec_ref_known(v___x_2243_, 2);
lean_del_object(v___x_2236_);
v___x_2251_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 1, v___x_2251_);
v___x_2253_ = v___x_2240_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_toMonitorResult_2238_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2258_, lean_object* v_job_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2258_, v_job_2259_);
lean_dec_ref(v_mctx_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2262_, lean_object* v_mctx_2263_, lean_object* v_job_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2263_, v_job_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2267_, lean_object* v_mctx_2268_, lean_object* v_job_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2267_, v_mctx_2268_, v_job_2269_);
lean_dec_ref(v_mctx_2268_);
return v_res_2271_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2285_, lean_object* v_build_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v_out_2298_; 
v___x_2288_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2289_ = lean_st_mk_ref(v___x_2288_);
v___x_2290_ = 0;
v___x_2291_ = 1;
v___x_2292_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2289_);
v___x_2293_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2292_, v___x_2289_);
v___x_2294_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2285_, v___x_2292_, v___x_2289_);
v___x_2295_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2296_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2294_, v_build_2286_, v___x_2295_);
lean_dec_ref(v___x_2294_);
v___x_2297_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2293_, v___x_2296_);
lean_dec_ref(v___x_2293_);
v_out_2298_ = lean_ctor_get(v___x_2297_, 1);
lean_inc_ref(v_out_2298_);
lean_dec_ref(v___x_2297_);
if (lean_obj_tag(v_out_2298_) == 0)
{
lean_dec_ref_known(v_out_2298_, 1);
return v___x_2290_;
}
else
{
lean_dec_ref_known(v_out_2298_, 1);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2299_, lean_object* v_build_2300_, lean_object* v_a_2301_){
_start:
{
uint8_t v_res_2302_; lean_object* v_r_2303_; 
v_res_2302_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2299_, v_build_2300_);
v_r_2303_ = lean_box(v_res_2302_);
return v_r_2303_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2304_, lean_object* v_ws_2305_, lean_object* v_build_2306_){
_start:
{
uint8_t v___x_2308_; 
v___x_2308_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2305_, v_build_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_ws_2310_, lean_object* v_build_2311_, lean_object* v_a_2312_){
_start:
{
uint8_t v_res_2313_; lean_object* v_r_2314_; 
v_res_2313_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2309_, v_ws_2310_, v_build_2311_);
v_r_2314_ = lean_box(v_res_2313_);
return v_r_2314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2315_, lean_object* v_build_2316_, lean_object* v_cfg_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2319_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2320_ = lean_st_mk_ref(v___x_2319_);
lean_inc(v___x_2320_);
v___x_2321_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2317_, v___x_2320_);
lean_inc_ref(v_cfg_2317_);
v___x_2322_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2315_, v_cfg_2317_, v___x_2320_);
v___x_2323_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2324_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2322_, v_build_2316_, v___x_2323_);
v___x_2325_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2321_, v___x_2324_);
v___x_2326_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2317_, v___x_2322_, v___x_2321_, v___x_2325_);
lean_dec_ref(v___x_2322_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2327_, lean_object* v_build_2328_, lean_object* v_cfg_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lake_Workspace_runBuild___redArg(v_ws_2327_, v_build_2328_, v_cfg_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2332_, lean_object* v_ws_2333_, lean_object* v_build_2334_, lean_object* v_cfg_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lake_Workspace_runBuild___redArg(v_ws_2333_, v_build_2334_, v_cfg_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_ws_2339_, lean_object* v_build_2340_, lean_object* v_cfg_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lake_Workspace_runBuild(v_00_u03b1_2338_, v_ws_2339_, v_build_2340_, v_cfg_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2344_, lean_object* v_cfg_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
lean_inc(v_a_2346_);
v___x_2348_ = l_Lake_Workspace_runBuild___redArg(v_a_2346_, v_build_2344_, v_cfg_2345_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2349_, lean_object* v_cfg_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lake_runBuild___redArg(v_build_2349_, v_cfg_2350_, v_a_2351_);
lean_dec(v_a_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2354_, lean_object* v_build_2355_, lean_object* v_cfg_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; 
lean_inc(v_a_2357_);
v___x_2359_ = l_Lake_Workspace_runBuild___redArg(v_a_2357_, v_build_2355_, v_cfg_2356_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2360_, lean_object* v_build_2361_, lean_object* v_cfg_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lake_runBuild(v_00_u03b1_2360_, v_build_2361_, v_cfg_2362_, v_a_2363_);
lean_dec(v_a_2363_);
return v_res_2365_;
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
