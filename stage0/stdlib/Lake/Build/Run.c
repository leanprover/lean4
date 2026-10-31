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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_exit(uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
uint8_t l_Lake_instOrdJobAction_ord(uint8_t, uint8_t);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
uint8_t lean_strict_and(uint8_t, uint8_t);
uint8_t l_Lake_Log_maxLv(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* l_IO_CancelToken_set(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_io_getenv(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "33"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " (Optional)"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__7_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Canceled"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0_value)}};
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Tracked package not found. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3;
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__4_value;
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__4_value)} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5_value;
static const lean_array_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = ": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "Build missing input-to-output mappings. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "- "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Some required targets logged failures:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__1;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__2;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__3;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Build completed successfully ("};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ").\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "All targets up-to-date ("};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " jobs"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "1 job"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_reportResult___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Nothing to build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_reportResult___closed__9_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__10;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__11;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__12;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg();
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___boxed(lean_object*);
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
static const lean_array_object l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0 = (const lean_object*)&l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "include"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean includes"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lean.h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "config.h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "version.h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mimalloc.h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__6_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__3_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__4_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__5_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__6_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Lean "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "MACOSX_DEPLOYMENT_TARGET"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "99.0"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_Workspace_checkNoBuild___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 1, 0, 0, 0)}};
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1_; lean_object* v___x_2_; 
v___x_1_ = 10493;
v___x_2_ = lean_box_uint32(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2(void){
_start:
{
uint32_t v___x_3_; lean_object* v___x_4_; 
v___x_3_ = 10491;
v___x_4_ = lean_box_uint32(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3(void){
_start:
{
uint32_t v___x_5_; lean_object* v___x_6_; 
v___x_5_ = 10431;
v___x_6_ = lean_box_uint32(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4(void){
_start:
{
uint32_t v___x_7_; lean_object* v___x_8_; 
v___x_7_ = 10367;
v___x_8_ = lean_box_uint32(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5(void){
_start:
{
uint32_t v___x_9_; lean_object* v___x_10_; 
v___x_9_ = 10463;
v___x_10_ = lean_box_uint32(v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6(void){
_start:
{
uint32_t v___x_11_; lean_object* v___x_12_; 
v___x_11_ = 10479;
v___x_12_ = lean_box_uint32(v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7(void){
_start:
{
uint32_t v___x_13_; lean_object* v___x_14_; 
v___x_13_ = 10487;
v___x_14_ = lean_box_uint32(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8(void){
_start:
{
uint32_t v___x_15_; lean_object* v___x_16_; 
v___x_15_ = 10494;
v___x_16_ = lean_box_uint32(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_17_ = lean_unsigned_to_nat(8u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8;
v___x_20_ = lean_array_push(v___x_18_, v___x_19_);
v___x_21_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7;
v___x_22_ = lean_array_push(v___x_20_, v___x_21_);
v___x_23_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6;
v___x_24_ = lean_array_push(v___x_22_, v___x_23_);
v___x_25_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5;
v___x_26_ = lean_array_push(v___x_24_, v___x_25_);
v___x_27_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4;
v___x_28_ = lean_array_push(v___x_26_, v___x_27_);
v___x_29_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3;
v___x_30_ = lean_array_push(v___x_28_, v___x_29_);
v___x_31_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2;
v___x_32_ = lean_array_push(v___x_30_, v___x_31_);
v___x_33_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1;
v___x_34_ = lean_array_push(v___x_32_, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object* v_out_36_, uint8_t v_outLv_37_, uint8_t v_useAnsi_38_, lean_object* v_e_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_logToStream(v_e_39_, v_out_36_, v_outLv_37_, v_useAnsi_38_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object* v_out_42_, lean_object* v_outLv_43_, lean_object* v_useAnsi_44_, lean_object* v_e_45_, lean_object* v___y_46_){
_start:
{
uint8_t v_outLv_boxed_47_; uint8_t v_useAnsi_boxed_48_; lean_object* v_res_49_; 
v_outLv_boxed_47_ = lean_unbox(v_outLv_43_);
v_useAnsi_boxed_48_ = lean_unbox(v_useAnsi_44_);
v_res_49_ = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(v_out_42_, v_outLv_boxed_47_, v_useAnsi_boxed_48_, v_e_45_);
lean_dec_ref(v_e_45_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object* v_ctx_50_){
_start:
{
lean_object* v_out_51_; uint8_t v_outLv_52_; uint8_t v_useAnsi_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___f_56_; 
v_out_51_ = lean_ctor_get(v_ctx_50_, 1);
lean_inc_ref(v_out_51_);
v_outLv_52_ = lean_ctor_get_uint8(v_ctx_50_, sizeof(void*)*4);
v_useAnsi_53_ = lean_ctor_get_uint8(v_ctx_50_, sizeof(void*)*4 + 4);
lean_dec_ref(v_ctx_50_);
v___x_54_ = lean_box(v_outLv_52_);
v___x_55_ = lean_box(v_useAnsi_53_);
v___f_56_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed), 5, 3);
lean_closure_set(v___f_56_, 0, v_out_51_);
lean_closure_set(v___f_56_, 1, v___x_54_);
lean_closure_set(v___f_56_, 2, v___x_55_);
return v___f_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* v_ctx_57_, lean_object* v_s_58_, lean_object* v_self_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_3(v_self_59_, v_ctx_57_, v_s_58_, lean_box(0));
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object* v_ctx_62_, lean_object* v_s_63_, lean_object* v_self_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(v_ctx_62_, v_s_63_, v_self_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* v_00_u03b1_67_, lean_object* v_ctx_68_, lean_object* v_s_69_, lean_object* v_self_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_apply_3(v_self_70_, v_ctx_68_, v_s_69_, lean_box(0));
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object* v_00_u03b1_73_, lean_object* v_ctx_74_, lean_object* v_s_75_, lean_object* v_self_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run(v_00_u03b1_73_, v_ctx_74_, v_s_75_, v_self_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* v_out_81_){
_start:
{
lean_object* v_flush_83_; lean_object* v___x_84_; 
v_flush_83_ = lean_ctor_get(v_out_81_, 0);
lean_inc_ref(v_flush_83_);
lean_dec_ref(v_out_81_);
v___x_84_ = lean_apply_1(v_flush_83_, lean_box(0));
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_84_, 1);
return v_a_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec_ref_known(v___x_84_, 1);
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object* v_out_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lake_Build_Run_0__Lake_flush(v_out_87_);
return v_res_89_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_box(0);
v___x_91_ = l_instMonadBaseIO;
v___x_92_ = l_instInhabitedOfMonad___redArg(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16(void){
_start:
{
uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = 1;
v___x_123_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__16, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16);
v___x_126_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_127_ = lean_string_append(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_130_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__17, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
v___x_131_ = lean_string_append(v___x_130_, v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* v_out_133_, lean_object* v_s_134_){
_start:
{
lean_object* v_putStr_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_putStr_136_ = lean_ctor_get(v_out_133_, 4);
lean_inc_ref(v_putStr_136_);
lean_dec_ref(v_out_133_);
v___x_137_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
lean_inc_ref(v_s_134_);
v___x_138_ = lean_apply_2(v_putStr_136_, v_s_134_, lean_box(0));
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; 
lean_dec_ref(v_s_134_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
return v_a_139_;
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_164_; 
v_a_140_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_164_ == 0)
{
v___x_142_ = v___x_138_;
v_isShared_143_ = v_isSharedCheck_164_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_164_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_144_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_145_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_146_ = lean_unsigned_to_nat(82u);
v___x_147_ = lean_unsigned_to_nat(4u);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_150_ = lean_io_error_to_string(v_a_140_);
v___x_151_ = lean_string_append(v___x_149_, v___x_150_);
lean_dec_ref(v___x_150_);
v___x_152_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_153_ = lean_string_append(v___x_151_, v___x_152_);
v___x_154_ = l_String_quote(v_s_134_);
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 3);
lean_ctor_set(v___x_142_, 0, v___x_154_);
v___x_156_ = v___x_142_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_163_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_186__overap_161_; lean_object* v___x_162_; 
v___x_157_ = l_Std_Format_defWidth;
v___x_158_ = l_Std_Format_pretty(v___x_156_, v___x_157_, v___x_148_, v___x_148_);
v___x_159_ = lean_string_append(v___x_153_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l_mkPanicMessageWithDecl(v___x_144_, v___x_145_, v___x_146_, v___x_147_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_186__overap_161_ = l_panic___redArg(v___x_137_, v___x_160_);
v___x_162_ = lean_apply_1(v___x_186__overap_161_, lean_box(0));
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object* v_out_165_, lean_object* v_s_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Lake_Build_Run_0__Lake_print_x21(v_out_165_, v_s_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* v_s_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_val_174_; lean_object* v_out_176_; lean_object* v_putStr_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_out_176_ = lean_ctor_get(v_a_170_, 1);
v_putStr_177_ = lean_ctor_get(v_out_176_, 4);
v___x_178_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
lean_inc_ref(v_putStr_177_);
lean_inc_ref(v_s_169_);
v___x_179_ = lean_apply_2(v_putStr_177_, v_s_169_, lean_box(0));
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; 
lean_dec_ref(v_s_169_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v_val_174_ = v_a_180_;
goto v___jp_173_;
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_205_; 
v_a_181_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_205_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_205_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_205_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_185_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_186_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_187_ = lean_unsigned_to_nat(82u);
v___x_188_ = lean_unsigned_to_nat(4u);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_191_ = lean_io_error_to_string(v_a_181_);
v___x_192_ = lean_string_append(v___x_190_, v___x_191_);
lean_dec_ref(v___x_191_);
v___x_193_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = l_String_quote(v_s_169_);
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 3);
lean_ctor_set(v___x_183_, 0, v___x_195_);
v___x_197_ = v___x_183_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_204_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_1132__overap_202_; lean_object* v___x_203_; 
v___x_198_ = l_Std_Format_defWidth;
v___x_199_ = l_Std_Format_pretty(v___x_197_, v___x_198_, v___x_189_, v___x_189_);
v___x_200_ = lean_string_append(v___x_194_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_mkPanicMessageWithDecl(v___x_185_, v___x_186_, v___x_187_, v___x_188_, v___x_200_);
lean_dec_ref(v___x_200_);
v___x_1132__overap_202_ = l_panic___redArg(v___x_178_, v___x_201_);
v___x_203_ = lean_apply_1(v___x_1132__overap_202_, lean_box(0));
v_val_174_ = v___x_203_;
goto v___jp_173_;
}
}
}
v___jp_173_:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_val_174_);
lean_ctor_set(v___x_175_, 1, v_a_171_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object* v_s_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lake_Build_Run_0__Lake_Monitor_print(v_s_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_a_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_val_215_; lean_object* v_out_217_; lean_object* v_flush_218_; lean_object* v___x_219_; 
v_out_217_ = lean_ctor_get(v_a_211_, 1);
v_flush_218_ = lean_ctor_get(v_out_217_, 0);
lean_inc_ref(v_flush_218_);
v___x_219_ = lean_apply_1(v_flush_218_, lean_box(0));
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_219_, 1);
v_val_215_ = v_a_220_;
goto v___jp_214_;
}
else
{
lean_object* v___x_221_; 
lean_dec_ref_known(v___x_219_, 1);
v___x_221_ = lean_box(0);
v_val_215_ = v___x_221_;
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_val_215_);
lean_ctor_set(v___x_216_, 1, v_a_212_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lake_Build_Run_0__Lake_Monitor_flush(v_a_222_, v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* v_msg_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_7771__overap_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_7771__overap_229_ = lean_panic_fn_borrowed(v___x_228_, v_msg_226_);
v___x_230_ = lean_apply_1(v___x_7771__overap_229_, lean_box(0));
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object* v_msg_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v_msg_231_);
return v_res_233_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_235_ = lean_array_get_size(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* v_running_242_, lean_object* v_unfinished_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
uint8_t v_showProgress_250_; 
v_showProgress_250_ = lean_ctor_get_uint8(v_a_244_, sizeof(void*)*4 + 5);
if (v_showProgress_250_ == 0)
{
goto v___jp_247_;
}
else
{
uint8_t v_useAnsi_251_; 
v_useAnsi_251_ = lean_ctor_get_uint8(v_a_244_, sizeof(void*)*4 + 4);
if (v_useAnsi_251_ == 0)
{
goto v___jp_247_;
}
else
{
lean_object* v_jobNo_252_; lean_object* v_totalJobs_253_; uint8_t v_wantsRebuild_254_; lean_object* v_failures_255_; lean_object* v_resetCtrl_256_; lean_object* v_lastUpdate_257_; lean_object* v_spinnerIdx_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_347_; 
v_jobNo_252_ = lean_ctor_get(v_a_245_, 0);
v_totalJobs_253_ = lean_ctor_get(v_a_245_, 1);
v_wantsRebuild_254_ = lean_ctor_get_uint8(v_a_245_, sizeof(void*)*6);
v_failures_255_ = lean_ctor_get(v_a_245_, 2);
v_resetCtrl_256_ = lean_ctor_get(v_a_245_, 3);
v_lastUpdate_257_ = lean_ctor_get(v_a_245_, 4);
v_spinnerIdx_258_ = lean_ctor_get(v_a_245_, 5);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_245_);
if (v_isSharedCheck_347_ == 0)
{
v___x_260_ = v_a_245_;
v_isShared_261_ = v_isSharedCheck_347_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_spinnerIdx_258_);
lean_inc(v_lastUpdate_257_);
lean_inc(v_resetCtrl_256_);
lean_inc(v_failures_255_);
lean_inc(v_totalJobs_253_);
lean_inc(v_jobNo_252_);
lean_dec(v_a_245_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_347_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_out_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v_out_262_ = lean_ctor_get(v_a_244_, 1);
v___x_263_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_264_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
v___x_265_ = lean_array_fget_borrowed(v___x_263_, v_spinnerIdx_258_);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = l_Fin_add(v___x_264_, v_spinnerIdx_258_, v___x_266_);
lean_dec(v_spinnerIdx_258_);
v___x_268_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(v_totalJobs_253_);
lean_inc(v_jobNo_252_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 5, v___x_267_);
lean_ctor_set(v___x_260_, 3, v___x_268_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_jobNo_252_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_totalJobs_253_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_failures_255_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_lastUpdate_257_);
lean_ctor_set(v_reuseFailAlloc_346_, 5, v___x_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*6, v_wantsRebuild_254_);
v___x_270_ = v_reuseFailAlloc_346_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v_val_272_; lean_object* v___y_280_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_array_get_size(v_running_242_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_caption_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = lean_array_get_size(v_unfinished_243_);
v___x_330_ = lean_nat_sub(v___x_329_, v___x_266_);
v___x_331_ = lean_array_fget_borrowed(v_unfinished_243_, v___x_330_);
lean_dec(v___x_330_);
v_caption_332_ = lean_ctor_get(v___x_331_, 2);
v___x_333_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_334_ = lean_string_append(v___x_333_, v_caption_332_);
v___y_280_ = v___x_334_;
goto v___jp_279_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_caption_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_335_ = lean_nat_sub(v___x_327_, v___x_266_);
v___x_336_ = lean_array_fget_borrowed(v_running_242_, v___x_335_);
v_caption_337_ = lean_ctor_get(v___x_336_, 2);
v___x_338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_339_ = lean_string_append(v___x_338_, v_caption_337_);
v___x_340_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
v___x_341_ = lean_string_append(v___x_339_, v___x_340_);
v___x_342_ = l_Nat_reprFast(v___x_335_);
v___x_343_ = lean_string_append(v___x_341_, v___x_342_);
lean_dec_ref(v___x_342_);
v___x_344_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
v___y_280_ = v___x_345_;
goto v___jp_279_;
}
v___jp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_val_272_);
lean_ctor_set(v___x_273_, 1, v___x_270_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v_flush_275_; lean_object* v___x_276_; 
v_flush_275_ = lean_ctor_get(v_out_262_, 0);
lean_inc_ref(v_flush_275_);
v___x_276_ = lean_apply_1(v_flush_275_, lean_box(0));
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v_val_272_ = v_a_277_;
goto v___jp_271_;
}
else
{
lean_object* v___x_278_; 
lean_dec_ref_known(v___x_276_, 1);
v___x_278_ = lean_box(0);
v_val_272_ = v___x_278_;
goto v___jp_271_;
}
}
v___jp_279_:
{
lean_object* v_putStr_281_; lean_object* v___x_282_; uint32_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_putStr_281_ = lean_ctor_get(v_out_262_, 4);
v___x_282_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_283_ = lean_unbox_uint32(v___x_265_);
v___x_284_ = lean_string_push(v___x_282_, v___x_283_);
v___x_285_ = lean_string_append(v_resetCtrl_256_, v___x_284_);
lean_dec_ref(v___x_284_);
v___x_286_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
v___x_288_ = l_Nat_reprFast(v_jobNo_252_);
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_291_ = lean_string_append(v___x_289_, v___x_290_);
v___x_292_ = l_Nat_reprFast(v_totalJobs_253_);
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
v___x_296_ = lean_string_append(v___x_295_, v___y_280_);
lean_dec_ref(v___y_280_);
lean_inc_ref(v_putStr_281_);
lean_inc_ref(v___x_296_);
v___x_297_ = lean_apply_2(v_putStr_281_, v___x_296_, lean_box(0));
if (lean_obj_tag(v___x_297_) == 0)
{
lean_dec_ref_known(v___x_297_, 1);
lean_dec_ref(v___x_296_);
goto v___jp_274_;
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_325_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_325_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_325_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_325_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_302_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_303_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_304_ = lean_unsigned_to_nat(82u);
v___x_305_ = lean_unsigned_to_nat(4u);
v___x_306_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_309_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_308_, v_useAnsi_251_);
v___x_310_ = lean_string_append(v___x_306_, v___x_309_);
lean_dec_ref(v___x_309_);
v___x_311_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_312_ = lean_string_append(v___x_310_, v___x_311_);
v___x_313_ = lean_io_error_to_string(v_a_298_);
v___x_314_ = lean_string_append(v___x_312_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = lean_string_append(v___x_314_, v___x_294_);
v___x_316_ = l_String_quote(v___x_296_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 3);
lean_ctor_set(v___x_300_, 0, v___x_316_);
v___x_318_ = v___x_300_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_324_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_319_ = l_Std_Format_defWidth;
v___x_320_ = l_Std_Format_pretty(v___x_318_, v___x_319_, v___x_307_, v___x_307_);
v___x_321_ = lean_string_append(v___x_315_, v___x_320_);
lean_dec_ref(v___x_320_);
v___x_322_ = l_mkPanicMessageWithDecl(v___x_302_, v___x_303_, v___x_304_, v___x_305_, v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_322_);
goto v___jp_274_;
}
}
}
}
}
}
}
}
v___jp_247_:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v_a_245_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* v_running_348_, lean_object* v_unfinished_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_348_, v_unfinished_349_, v_a_350_, v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_unfinished_349_);
lean_dec_ref(v_running_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* v_running_354_, lean_object* v_unfinished_355_, lean_object* v_h_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_354_, v_unfinished_355_, v_a_357_, v_a_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* v_running_361_, lean_object* v_unfinished_362_, lean_object* v_h_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(v_running_361_, v_unfinished_362_, v_h_363_, v_a_364_, v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec_ref(v_unfinished_362_);
lean_dec_ref(v_running_361_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object* v_ms_371_){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(10000u);
v___x_373_ = lean_nat_dec_lt(v___x_372_, v_ms_371_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(1000u);
v___x_375_ = lean_nat_dec_lt(v___x_374_, v_ms_371_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = l_Nat_reprFast(v_ms_371_);
v___x_377_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0));
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_379_ = lean_nat_div(v_ms_371_, v___x_374_);
v___x_380_ = l_Nat_reprFast(v___x_379_);
v___x_381_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1));
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
v___x_383_ = lean_unsigned_to_nat(50u);
v___x_384_ = lean_nat_add(v_ms_371_, v___x_383_);
lean_dec(v_ms_371_);
v___x_385_ = lean_unsigned_to_nat(100u);
v___x_386_ = lean_nat_div(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_unsigned_to_nat(10u);
v___x_388_ = lean_nat_mod(v___x_386_, v___x_387_);
lean_dec(v___x_386_);
v___x_389_ = l_Nat_reprFast(v___x_388_);
v___x_390_ = lean_string_append(v___x_382_, v___x_389_);
lean_dec_ref(v___x_389_);
v___x_391_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_392_ = lean_string_append(v___x_390_, v___x_391_);
return v___x_392_;
}
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = lean_unsigned_to_nat(1000u);
v___x_394_ = lean_nat_div(v_ms_371_, v___x_393_);
lean_dec(v_ms_371_);
v___x_395_ = l_Nat_reprFast(v___x_394_);
v___x_396_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* v_out_398_, uint8_t v___y_399_, uint8_t v_useAnsi_400_, lean_object* v_as_401_, size_t v_i_402_, size_t v_stop_403_, lean_object* v_b_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_eq(v_i_402_, v_stop_403_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; size_t v___x_410_; size_t v___x_411_; 
v___x_408_ = lean_array_uget_borrowed(v_as_401_, v_i_402_);
lean_inc_ref(v_out_398_);
v___x_409_ = l_Lake_logToStream(v___x_408_, v_out_398_, v___y_399_, v_useAnsi_400_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_402_, v___x_410_);
v_i_402_ = v___x_411_;
v_b_404_ = v___x_409_;
goto _start;
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v_out_398_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_b_404_);
lean_ctor_set(v___x_413_, 1, v___y_405_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* v_out_414_, lean_object* v___y_415_, lean_object* v_useAnsi_416_, lean_object* v_as_417_, lean_object* v_i_418_, lean_object* v_stop_419_, lean_object* v_b_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
uint8_t v___y_14242__boxed_423_; uint8_t v_useAnsi_14243__boxed_424_; size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v___y_14242__boxed_423_ = lean_unbox(v___y_415_);
v_useAnsi_14243__boxed_424_ = lean_unbox(v_useAnsi_416_);
v_i_boxed_425_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_414_, v___y_14242__boxed_423_, v_useAnsi_14243__boxed_424_, v_as_417_, v_i_boxed_425_, v_stop_boxed_426_, v_b_420_, v___y_421_);
lean_dec_ref(v_as_417_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___y_442_; lean_object* v___y_446_; lean_object* v_val_447_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v_jobNo_457_; lean_object* v_totalJobs_458_; uint8_t v_wantsRebuild_459_; lean_object* v_failures_460_; lean_object* v_resetCtrl_461_; lean_object* v_lastUpdate_462_; lean_object* v_spinnerIdx_463_; lean_object* v_out_464_; uint8_t v_outLv_465_; uint8_t v_failLv_466_; uint8_t v_minAction_467_; uint8_t v_showOptional_468_; uint8_t v_useAnsi_469_; uint8_t v_showProgress_470_; uint8_t v_showTime_471_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; uint8_t v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; uint8_t v___y_491_; lean_object* v___y_492_; uint8_t v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; uint8_t v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; uint8_t v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; lean_object* v_task_570_; lean_object* v_caption_571_; uint8_t v_optional_572_; uint8_t v___y_574_; uint8_t v___y_575_; uint8_t v___y_576_; lean_object* v___y_577_; uint8_t v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; uint32_t v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; uint8_t v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; uint8_t v___y_611_; uint8_t v___y_612_; uint8_t v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint32_t v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; uint8_t v___y_626_; uint8_t v___y_627_; uint8_t v___y_628_; lean_object* v___y_629_; uint8_t v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint32_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_647_; uint8_t v___y_648_; uint8_t v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; uint32_t v___y_659_; uint8_t v___y_663_; uint8_t v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; uint8_t v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_679_; uint8_t v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; uint8_t v___y_689_; uint8_t v___y_692_; uint8_t v___y_693_; lean_object* v___y_694_; uint8_t v___y_695_; uint8_t v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; uint8_t v___y_706_; uint8_t v___y_707_; lean_object* v___y_708_; uint8_t v___y_709_; uint8_t v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; uint8_t v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v___y_759_; uint8_t v___y_760_; lean_object* v___y_761_; uint8_t v___y_762_; uint8_t v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; uint8_t v___y_768_; uint8_t v___y_783_; uint8_t v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; uint8_t v___y_788_; uint8_t v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; uint8_t v___y_796_; uint8_t v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_809_; lean_object* v___x_821_; lean_object* v_a_822_; 
v_jobNo_457_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_jobNo_457_);
v_totalJobs_458_ = lean_ctor_get(v_a_439_, 1);
lean_inc(v_totalJobs_458_);
v_wantsRebuild_459_ = lean_ctor_get_uint8(v_a_439_, sizeof(void*)*6);
v_failures_460_ = lean_ctor_get(v_a_439_, 2);
v_resetCtrl_461_ = lean_ctor_get(v_a_439_, 3);
v_lastUpdate_462_ = lean_ctor_get(v_a_439_, 4);
v_spinnerIdx_463_ = lean_ctor_get(v_a_439_, 5);
v_out_464_ = lean_ctor_get(v_a_438_, 1);
v_outLv_465_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4);
v_failLv_466_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4 + 1);
v_minAction_467_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4 + 2);
v_showOptional_468_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4 + 3);
v_useAnsi_469_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4 + 4);
v_showProgress_470_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4 + 5);
v_showTime_471_ = lean_ctor_get_uint8(v_a_438_, sizeof(void*)*4 + 6);
v_task_570_ = lean_ctor_get(v_job_437_, 0);
lean_inc_ref(v_task_570_);
v_caption_571_ = lean_ctor_get(v_job_437_, 2);
lean_inc_ref(v_caption_571_);
v_optional_572_ = lean_ctor_get_uint8(v_job_437_, sizeof(void*)*3);
lean_dec_ref(v_job_437_);
v___x_821_ = lean_task_get_own(v_task_570_);
v_a_822_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___y_809_ = v_a_822_;
goto v___jp_808_;
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___y_442_);
return v___x_444_;
}
v___jp_445_:
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_val_447_);
lean_ctor_set(v___x_448_, 1, v___y_446_);
return v___x_448_;
}
v___jp_449_:
{
lean_object* v_out_452_; lean_object* v_flush_453_; lean_object* v___x_454_; 
v_out_452_ = lean_ctor_get(v___y_450_, 1);
v_flush_453_ = lean_ctor_get(v_out_452_, 0);
lean_inc_ref(v_flush_453_);
v___x_454_ = lean_apply_1(v_flush_453_, lean_box(0));
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___y_446_ = v___y_451_;
v_val_447_ = v_a_455_;
goto v___jp_445_;
}
else
{
lean_object* v___x_456_; 
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = lean_box(0);
v___y_446_ = v___y_451_;
v_val_447_ = v___x_456_;
goto v___jp_445_;
}
}
v___jp_472_:
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_lt(v___y_476_, v___y_473_);
lean_dec(v___y_476_);
if (v___x_479_ == 0)
{
lean_dec_ref(v___y_477_);
lean_dec(v___y_473_);
v___y_450_ = v___y_475_;
v___y_451_ = v___y_474_;
goto v___jp_449_;
}
else
{
lean_object* v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v_snd_484_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___y_473_);
lean_dec(v___y_473_);
lean_inc_ref(v_out_464_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_464_, v___y_478_, v_useAnsi_469_, v___y_477_, v___x_481_, v___x_482_, v___x_480_, v___y_474_);
lean_dec_ref(v___y_477_);
v_snd_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_snd_484_);
lean_dec_ref(v___x_483_);
v___y_450_ = v___y_475_;
v___y_451_ = v_snd_484_;
goto v___jp_449_;
}
}
v___jp_485_:
{
if (v___y_491_ == 0)
{
lean_dec_ref(v___y_492_);
lean_dec(v___y_488_);
lean_dec(v___y_487_);
v___y_450_ = v___y_489_;
v___y_451_ = v___y_490_;
goto v___jp_449_;
}
else
{
if (v___y_486_ == 0)
{
v___y_473_ = v___y_487_;
v___y_474_ = v___y_490_;
v___y_475_ = v___y_489_;
v___y_476_ = v___y_488_;
v___y_477_ = v___y_492_;
v___y_478_ = v_outLv_465_;
goto v___jp_472_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = 0;
v___y_473_ = v___y_487_;
v___y_474_ = v___y_490_;
v___y_475_ = v___y_489_;
v___y_476_ = v___y_488_;
v___y_477_ = v___y_492_;
v___y_478_ = v___x_493_;
goto v___jp_472_;
}
}
}
v___jp_494_:
{
lean_object* v_out_504_; lean_object* v_jobNo_505_; lean_object* v_totalJobs_506_; uint8_t v_wantsRebuild_507_; lean_object* v_failures_508_; lean_object* v_resetCtrl_509_; lean_object* v_lastUpdate_510_; lean_object* v_spinnerIdx_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_557_; 
v_out_504_ = lean_ctor_get(v___y_497_, 1);
v_jobNo_505_ = lean_ctor_get(v___y_502_, 0);
v_totalJobs_506_ = lean_ctor_get(v___y_502_, 1);
v_wantsRebuild_507_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*6);
v_failures_508_ = lean_ctor_get(v___y_502_, 2);
v_resetCtrl_509_ = lean_ctor_get(v___y_502_, 3);
v_lastUpdate_510_ = lean_ctor_get(v___y_502_, 4);
v_spinnerIdx_511_ = lean_ctor_get(v___y_502_, 5);
v_isSharedCheck_557_ = !lean_is_exclusive(v___y_502_);
if (v_isSharedCheck_557_ == 0)
{
v___x_513_ = v___y_502_;
v_isShared_514_ = v_isSharedCheck_557_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_spinnerIdx_511_);
lean_inc(v_lastUpdate_510_);
lean_inc(v_resetCtrl_509_);
lean_inc(v_failures_508_);
lean_inc(v_totalJobs_506_);
lean_inc(v_jobNo_505_);
lean_dec(v___y_502_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_557_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_putStr_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v_putStr_515_ = lean_ctor_get(v_out_504_, 4);
v___x_516_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 3, v___x_516_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_jobNo_505_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_totalJobs_506_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_failures_508_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_lastUpdate_510_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_spinnerIdx_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*6, v_wantsRebuild_507_);
v___x_518_ = v_reuseFailAlloc_556_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = lean_string_append(v_resetCtrl_509_, v___y_503_);
lean_dec_ref(v___y_503_);
v___x_520_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
lean_inc_ref(v_putStr_515_);
lean_inc_ref(v___x_521_);
v___x_522_ = lean_apply_2(v_putStr_515_, v___x_521_, lean_box(0));
if (lean_obj_tag(v___x_522_) == 0)
{
lean_dec_ref_known(v___x_522_, 1);
lean_dec_ref(v___x_521_);
v___y_486_ = v___y_495_;
v___y_487_ = v___y_496_;
v___y_488_ = v___y_498_;
v___y_489_ = v___y_497_;
v___y_490_ = v___x_518_;
v___y_491_ = v___y_499_;
v___y_492_ = v___y_501_;
goto v___jp_485_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_555_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_555_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_555_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_555_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_527_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_528_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_529_ = lean_unsigned_to_nat(82u);
v___x_530_ = lean_unsigned_to_nat(4u);
v___x_531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_532_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_533_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc(v___y_498_);
v___x_534_ = l_Lean_Name_num___override(v___x_533_, v___y_498_);
v___x_535_ = l_Lean_Name_str___override(v___x_534_, v___x_532_);
v___x_536_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_537_ = l_Lean_Name_str___override(v___x_535_, v___x_536_);
v___x_538_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_537_, v___y_500_);
v___x_539_ = lean_string_append(v___x_531_, v___x_538_);
lean_dec_ref(v___x_538_);
v___x_540_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
v___x_542_ = lean_io_error_to_string(v_a_523_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
v___x_546_ = l_String_quote(v___x_521_);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 3);
lean_ctor_set(v___x_525_, 0, v___x_546_);
v___x_548_ = v___x_525_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_554_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_549_ = l_Std_Format_defWidth;
lean_inc_n(v___y_498_, 2);
v___x_550_ = l_Std_Format_pretty(v___x_548_, v___x_549_, v___y_498_, v___y_498_);
v___x_551_ = lean_string_append(v___x_545_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_mkPanicMessageWithDecl(v___x_527_, v___x_528_, v___x_529_, v___x_530_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_552_);
v___y_486_ = v___y_495_;
v___y_487_ = v___y_496_;
v___y_488_ = v___y_498_;
v___y_489_ = v___y_497_;
v___y_490_ = v___x_518_;
v___y_491_ = v___y_499_;
v___y_492_ = v___y_501_;
goto v___jp_485_;
}
}
}
}
}
}
v___jp_558_:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lake_Ansi_chalk(v___y_568_, v___y_564_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_568_);
v___y_495_ = v___y_559_;
v___y_496_ = v___y_560_;
v___y_497_ = v___y_562_;
v___y_498_ = v___y_561_;
v___y_499_ = v___y_563_;
v___y_500_ = v___y_567_;
v___y_501_ = v___y_566_;
v___y_502_ = v___y_565_;
v___y_503_ = v___x_569_;
goto v___jp_494_;
}
v___jp_573_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_588_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_589_ = lean_string_push(v___x_588_, v___y_581_);
v___x_590_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
v___x_592_ = l_Nat_reprFast(v_jobNo_457_);
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
lean_dec_ref(v___x_592_);
v___x_594_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_595_ = lean_string_append(v___x_593_, v___x_594_);
v___x_596_ = l_Nat_reprFast(v_totalJobs_458_);
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = lean_string_append(v___x_599_, v___y_583_);
v___x_601_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
v___x_603_ = lean_string_append(v___x_602_, v___y_586_);
lean_dec_ref(v___y_586_);
v___x_604_ = lean_string_append(v___x_603_, v___x_601_);
v___x_605_ = lean_string_append(v___x_604_, v_caption_571_);
lean_dec_ref(v_caption_571_);
v___x_606_ = lean_string_append(v___x_605_, v___y_587_);
lean_dec_ref(v___y_587_);
if (v_useAnsi_469_ == 0)
{
v___y_495_ = v___y_575_;
v___y_496_ = v___y_580_;
v___y_497_ = v___y_577_;
v___y_498_ = v___y_582_;
v___y_499_ = v___y_578_;
v___y_500_ = v___y_585_;
v___y_501_ = v___y_584_;
v___y_502_ = v___y_579_;
v___y_503_ = v___x_606_;
goto v___jp_494_;
}
else
{
if (v___y_578_ == 0)
{
if (v___y_576_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_559_ = v___y_575_;
v___y_560_ = v___y_580_;
v___y_561_ = v___y_582_;
v___y_562_ = v___y_577_;
v___y_563_ = v___y_578_;
v___y_564_ = v___x_606_;
v___y_565_ = v___y_579_;
v___y_566_ = v___y_584_;
v___y_567_ = v___y_585_;
v___y_568_ = v___x_607_;
goto v___jp_558_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___y_559_ = v___y_575_;
v___y_560_ = v___y_580_;
v___y_561_ = v___y_582_;
v___y_562_ = v___y_577_;
v___y_563_ = v___y_578_;
v___y_564_ = v___x_606_;
v___y_565_ = v___y_579_;
v___y_566_ = v___y_584_;
v___y_567_ = v___y_585_;
v___y_568_ = v___x_608_;
goto v___jp_558_;
}
}
else
{
lean_object* v___x_609_; 
v___x_609_ = l_Lake_LogLevel_ansiColor(v___y_574_);
v___y_559_ = v___y_575_;
v___y_560_ = v___y_580_;
v___y_561_ = v___y_582_;
v___y_562_ = v___y_577_;
v___y_563_ = v___y_578_;
v___y_564_ = v___x_606_;
v___y_565_ = v___y_579_;
v___y_566_ = v___y_584_;
v___y_567_ = v___y_585_;
v___y_568_ = v___x_609_;
goto v___jp_558_;
}
}
}
v___jp_610_:
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_574_ = v___y_611_;
v___y_575_ = v___y_612_;
v___y_576_ = v___y_613_;
v___y_577_ = v___y_614_;
v___y_578_ = v___y_615_;
v___y_579_ = v___y_616_;
v___y_580_ = v___y_617_;
v___y_581_ = v___y_618_;
v___y_582_ = v___y_619_;
v___y_583_ = v___y_620_;
v___y_584_ = v___y_621_;
v___y_585_ = v___y_622_;
v___y_586_ = v___y_623_;
v___y_587_ = v___x_624_;
goto v___jp_573_;
}
v___jp_625_:
{
if (v_showTime_471_ == 0)
{
lean_dec(v___y_631_);
v___y_611_ = v___y_626_;
v___y_612_ = v___y_627_;
v___y_613_ = v___y_628_;
v___y_614_ = v___y_629_;
v___y_615_ = v___y_630_;
v___y_616_ = v___y_632_;
v___y_617_ = v___y_633_;
v___y_618_ = v___y_634_;
v___y_619_ = v___y_635_;
v___y_620_ = v___y_639_;
v___y_621_ = v___y_636_;
v___y_622_ = v___y_637_;
v___y_623_ = v___y_638_;
goto v___jp_610_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = lean_nat_dec_lt(v___y_635_, v___y_631_);
if (v___x_640_ == 0)
{
lean_dec(v___y_631_);
v___y_611_ = v___y_626_;
v___y_612_ = v___y_627_;
v___y_613_ = v___y_628_;
v___y_614_ = v___y_629_;
v___y_615_ = v___y_630_;
v___y_616_ = v___y_632_;
v___y_617_ = v___y_633_;
v___y_618_ = v___y_634_;
v___y_619_ = v___y_635_;
v___y_620_ = v___y_639_;
v___y_621_ = v___y_636_;
v___y_622_ = v___y_637_;
v___y_623_ = v___y_638_;
goto v___jp_610_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_641_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_642_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_631_);
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
lean_dec_ref(v___x_642_);
v___x_644_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___x_645_ = lean_string_append(v___x_643_, v___x_644_);
v___y_574_ = v___y_626_;
v___y_575_ = v___y_627_;
v___y_576_ = v___y_628_;
v___y_577_ = v___y_629_;
v___y_578_ = v___y_630_;
v___y_579_ = v___y_632_;
v___y_580_ = v___y_633_;
v___y_581_ = v___y_634_;
v___y_582_ = v___y_635_;
v___y_583_ = v___y_639_;
v___y_584_ = v___y_636_;
v___y_585_ = v___y_637_;
v___y_586_ = v___y_638_;
v___y_587_ = v___x_645_;
goto v___jp_573_;
}
}
}
v___jp_646_:
{
if (v_optional_572_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_626_ = v___y_647_;
v___y_627_ = v___y_648_;
v___y_628_ = v___y_649_;
v___y_629_ = v___y_650_;
v___y_630_ = v___y_651_;
v___y_631_ = v___y_652_;
v___y_632_ = v___y_653_;
v___y_633_ = v___y_654_;
v___y_634_ = v___y_659_;
v___y_635_ = v___y_655_;
v___y_636_ = v___y_656_;
v___y_637_ = v___y_657_;
v___y_638_ = v___y_658_;
v___y_639_ = v___x_660_;
goto v___jp_625_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__7));
v___y_626_ = v___y_647_;
v___y_627_ = v___y_648_;
v___y_628_ = v___y_649_;
v___y_629_ = v___y_650_;
v___y_630_ = v___y_651_;
v___y_631_ = v___y_652_;
v___y_632_ = v___y_653_;
v___y_633_ = v___y_654_;
v___y_634_ = v___y_659_;
v___y_635_ = v___y_655_;
v___y_636_ = v___y_656_;
v___y_637_ = v___y_657_;
v___y_638_ = v___y_658_;
v___y_639_ = v___x_661_;
goto v___jp_625_;
}
}
v___jp_662_:
{
if (v___y_669_ == 0)
{
if (v___y_666_ == 0)
{
uint32_t v___x_675_; 
v___x_675_ = 10004;
v___y_647_ = v___y_664_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_666_;
v___y_650_ = v___y_668_;
v___y_651_ = v___y_669_;
v___y_652_ = v___y_673_;
v___y_653_ = v___y_672_;
v___y_654_ = v___y_665_;
v___y_655_ = v___y_667_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_674_;
v___y_659_ = v___x_675_;
goto v___jp_646_;
}
else
{
uint32_t v___x_676_; 
v___x_676_ = 8856;
v___y_647_ = v___y_664_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_666_;
v___y_650_ = v___y_668_;
v___y_651_ = v___y_669_;
v___y_652_ = v___y_673_;
v___y_653_ = v___y_672_;
v___y_654_ = v___y_665_;
v___y_655_ = v___y_667_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_674_;
v___y_659_ = v___x_676_;
goto v___jp_646_;
}
}
else
{
uint32_t v___x_677_; 
v___x_677_ = l_Lake_LogLevel_icon(v___y_664_);
v___y_647_ = v___y_664_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_666_;
v___y_650_ = v___y_668_;
v___y_651_ = v___y_669_;
v___y_652_ = v___y_673_;
v___y_653_ = v___y_672_;
v___y_654_ = v___y_665_;
v___y_655_ = v___y_667_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_674_;
v___y_659_ = v___x_677_;
goto v___jp_646_;
}
}
v___jp_678_:
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__8));
v___y_663_ = v___y_680_;
v___y_664_ = v___y_679_;
v___y_665_ = v___y_681_;
v___y_666_ = v___y_682_;
v___y_667_ = v___y_683_;
v___y_668_ = v___y_684_;
v___y_669_ = v___y_685_;
v___y_670_ = v___y_689_;
v___y_671_ = v___y_688_;
v___y_672_ = v___y_687_;
v___y_673_ = v___y_686_;
v___y_674_ = v___x_690_;
goto v___jp_662_;
}
v___jp_691_:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lake_JobAction_verb(v___y_693_, v___y_695_);
v___y_663_ = v___y_693_;
v___y_664_ = v___y_692_;
v___y_665_ = v___y_694_;
v___y_666_ = v___y_696_;
v___y_667_ = v___y_697_;
v___y_668_ = v___y_698_;
v___y_669_ = v___y_699_;
v___y_670_ = v___y_703_;
v___y_671_ = v___y_702_;
v___y_672_ = v___y_701_;
v___y_673_ = v___y_700_;
v___y_674_ = v___x_704_;
goto v___jp_662_;
}
v___jp_705_:
{
if (v___y_713_ == 0)
{
if (v___y_710_ == 0)
{
if (v_showProgress_470_ == 0)
{
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_708_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_442_ = v___y_716_;
goto v___jp_441_;
}
else
{
if (v_useAnsi_469_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lake_instOrdJobAction_ord(v_minAction_467_, v___y_709_);
if (v___x_717_ == 2)
{
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_708_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_442_ = v___y_716_;
goto v___jp_441_;
}
else
{
v___y_692_ = v___y_707_;
v___y_693_ = v___y_706_;
v___y_694_ = v___y_708_;
v___y_695_ = v___y_709_;
v___y_696_ = v___y_710_;
v___y_697_ = v___y_712_;
v___y_698_ = v___y_711_;
v___y_699_ = v___y_713_;
v___y_700_ = v___y_715_;
v___y_701_ = v___y_716_;
v___y_702_ = v___y_714_;
v___y_703_ = v_showProgress_470_;
goto v___jp_691_;
}
}
else
{
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_708_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_442_ = v___y_716_;
goto v___jp_441_;
}
}
}
else
{
v___y_679_ = v___y_707_;
v___y_680_ = v___y_706_;
v___y_681_ = v___y_708_;
v___y_682_ = v___y_710_;
v___y_683_ = v___y_712_;
v___y_684_ = v___y_711_;
v___y_685_ = v___y_713_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_714_;
v___y_689_ = v___y_710_;
goto v___jp_678_;
}
}
else
{
if (v___y_710_ == 0)
{
v___y_692_ = v___y_707_;
v___y_693_ = v___y_706_;
v___y_694_ = v___y_708_;
v___y_695_ = v___y_709_;
v___y_696_ = v___y_710_;
v___y_697_ = v___y_712_;
v___y_698_ = v___y_711_;
v___y_699_ = v___y_713_;
v___y_700_ = v___y_715_;
v___y_701_ = v___y_716_;
v___y_702_ = v___y_714_;
v___y_703_ = v___y_713_;
goto v___jp_691_;
}
else
{
v___y_679_ = v___y_707_;
v___y_680_ = v___y_706_;
v___y_681_ = v___y_708_;
v___y_682_ = v___y_710_;
v___y_683_ = v___y_712_;
v___y_684_ = v___y_711_;
v___y_685_ = v___y_713_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_716_;
v___y_688_ = v___y_714_;
v___y_689_ = v___y_713_;
goto v___jp_678_;
}
}
}
v___jp_718_:
{
if (v_optional_572_ == 0)
{
v___y_706_ = v___y_719_;
v___y_707_ = v___y_720_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_722_;
v___y_710_ = v___y_723_;
v___y_711_ = v___y_724_;
v___y_712_ = v___y_725_;
v___y_713_ = v___y_729_;
v___y_714_ = v___y_726_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_727_;
goto v___jp_705_;
}
else
{
if (v_showOptional_468_ == 0)
{
lean_dec(v___y_728_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec(v___y_721_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_442_ = v___y_727_;
goto v___jp_441_;
}
else
{
v___y_706_ = v___y_719_;
v___y_707_ = v___y_720_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_722_;
v___y_710_ = v___y_723_;
v___y_711_ = v___y_724_;
v___y_712_ = v___y_725_;
v___y_713_ = v___y_729_;
v___y_714_ = v___y_726_;
v___y_715_ = v___y_728_;
v___y_716_ = v___y_727_;
goto v___jp_705_;
}
}
}
v___jp_730_:
{
if (v___y_732_ == 0)
{
if (v___y_737_ == 0)
{
v___y_719_ = v___y_732_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_737_;
goto v___jp_718_;
}
else
{
uint8_t v___x_742_; 
v___x_742_ = l_Lake_instOrdLogLevel_ord(v_outLv_465_, v___y_731_);
if (v___x_742_ == 2)
{
v___y_719_ = v___y_732_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_732_;
goto v___jp_718_;
}
else
{
v___y_719_ = v___y_732_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_737_;
goto v___jp_718_;
}
}
}
else
{
if (v_optional_572_ == 0)
{
lean_object* v_jobNo_743_; lean_object* v_totalJobs_744_; uint8_t v_wantsRebuild_745_; lean_object* v_failures_746_; lean_object* v_resetCtrl_747_; lean_object* v_lastUpdate_748_; lean_object* v_spinnerIdx_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_757_; 
v_jobNo_743_ = lean_ctor_get(v___y_741_, 0);
v_totalJobs_744_ = lean_ctor_get(v___y_741_, 1);
v_wantsRebuild_745_ = lean_ctor_get_uint8(v___y_741_, sizeof(void*)*6);
v_failures_746_ = lean_ctor_get(v___y_741_, 2);
v_resetCtrl_747_ = lean_ctor_get(v___y_741_, 3);
v_lastUpdate_748_ = lean_ctor_get(v___y_741_, 4);
v_spinnerIdx_749_ = lean_ctor_get(v___y_741_, 5);
v_isSharedCheck_757_ = !lean_is_exclusive(v___y_741_);
if (v_isSharedCheck_757_ == 0)
{
v___x_751_ = v___y_741_;
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_spinnerIdx_749_);
lean_inc(v_lastUpdate_748_);
lean_inc(v_resetCtrl_747_);
lean_inc(v_failures_746_);
lean_inc(v_totalJobs_744_);
lean_inc(v_jobNo_743_);
lean_dec(v___y_741_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_inc_ref(v_caption_571_);
v___x_753_ = lean_array_push(v_failures_746_, v_caption_571_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 2, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_jobNo_743_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_totalJobs_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_resetCtrl_747_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_lastUpdate_748_);
lean_ctor_set(v_reuseFailAlloc_756_, 5, v_spinnerIdx_749_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*6, v_wantsRebuild_745_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v___y_719_ = v___y_732_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___x_755_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_732_;
goto v___jp_718_;
}
}
}
else
{
v___y_719_ = v___y_732_;
v___y_720_ = v___y_731_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_732_;
goto v___jp_718_;
}
}
}
v___jp_758_:
{
if (v___y_763_ == 0)
{
v___y_731_ = v___y_760_;
v___y_732_ = v___y_759_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_768_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_765_;
v___y_738_ = v___y_766_;
v___y_739_ = v___y_767_;
v___y_740_ = v_a_438_;
v___y_741_ = v_a_439_;
goto v___jp_730_;
}
else
{
if (v_wantsRebuild_459_ == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_inc(v_spinnerIdx_463_);
lean_inc(v_lastUpdate_462_);
lean_inc_ref(v_resetCtrl_461_);
lean_inc_ref(v_failures_460_);
v_isSharedCheck_775_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; lean_object* v_unused_780_; lean_object* v_unused_781_; 
v_unused_776_ = lean_ctor_get(v_a_439_, 5);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_a_439_, 4);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_a_439_, 3);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_a_439_, 2);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_a_439_, 1);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_a_439_, 0);
lean_dec(v_unused_781_);
v___x_770_ = v_a_439_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_a_439_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
lean_inc(v_totalJobs_458_);
lean_inc(v_jobNo_457_);
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_jobNo_457_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_totalJobs_458_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_failures_460_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_resetCtrl_461_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_lastUpdate_462_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_spinnerIdx_463_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*6, v___y_763_);
v___y_731_ = v___y_760_;
v___y_732_ = v___y_759_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_768_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_765_;
v___y_738_ = v___y_766_;
v___y_739_ = v___y_767_;
v___y_740_ = v_a_438_;
v___y_741_ = v___x_773_;
goto v___jp_730_;
}
}
}
else
{
v___y_731_ = v___y_760_;
v___y_732_ = v___y_759_;
v___y_733_ = v___y_761_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_768_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_765_;
v___y_738_ = v___y_766_;
v___y_739_ = v___y_767_;
v___y_740_ = v_a_438_;
v___y_741_ = v_a_439_;
goto v___jp_730_;
}
}
}
v___jp_782_:
{
uint8_t v___x_793_; 
v___x_793_ = lean_strict_and(v___y_789_, v___y_792_);
if (v___y_783_ == 0)
{
v___y_759_ = v___x_793_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_788_;
v___y_764_ = v___y_787_;
v___y_765_ = v___y_789_;
v___y_766_ = v___y_791_;
v___y_767_ = v___y_790_;
v___y_768_ = v___y_783_;
goto v___jp_758_;
}
else
{
if (v___x_793_ == 0)
{
v___y_759_ = v___x_793_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_788_;
v___y_764_ = v___y_787_;
v___y_765_ = v___y_789_;
v___y_766_ = v___y_791_;
v___y_767_ = v___y_790_;
v___y_768_ = v___y_783_;
goto v___jp_758_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
v___y_759_ = v___x_793_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_788_;
v___y_764_ = v___y_787_;
v___y_765_ = v___y_789_;
v___y_766_ = v___y_791_;
v___y_767_ = v___y_790_;
v___y_768_ = v___x_794_;
goto v___jp_758_;
}
}
}
v___jp_795_:
{
uint8_t v___x_805_; 
v___x_805_ = l_Lake_instOrdLogLevel_ord(v_failLv_466_, v___y_796_);
if (v___x_805_ == 2)
{
uint8_t v___x_806_; 
v___x_806_ = 0;
v___y_783_ = v___y_797_;
v___y_784_ = v___y_796_;
v___y_785_ = v___y_798_;
v___y_786_ = v___y_799_;
v___y_787_ = v___y_801_;
v___y_788_ = v___y_800_;
v___y_789_ = v___y_804_;
v___y_790_ = v___y_803_;
v___y_791_ = v___y_802_;
v___y_792_ = v___x_806_;
goto v___jp_782_;
}
else
{
uint8_t v___x_807_; 
v___x_807_ = 1;
v___y_783_ = v___y_797_;
v___y_784_ = v___y_796_;
v___y_785_ = v___y_798_;
v___y_786_ = v___y_799_;
v___y_787_ = v___y_801_;
v___y_788_ = v___y_800_;
v___y_789_ = v___y_804_;
v___y_790_ = v___y_803_;
v___y_791_ = v___y_802_;
v___y_792_ = v___x_807_;
goto v___jp_782_;
}
}
v___jp_808_:
{
lean_object* v_log_810_; uint8_t v_action_811_; uint8_t v_wantsRebuild_812_; uint8_t v_canceled_813_; lean_object* v_buildTime_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_log_810_ = lean_ctor_get(v___y_809_, 0);
lean_inc_ref(v_log_810_);
v_action_811_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*3);
v_wantsRebuild_812_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*3 + 1);
v_canceled_813_ = lean_ctor_get_uint8(v___y_809_, sizeof(void*)*3 + 2);
v_buildTime_814_ = lean_ctor_get(v___y_809_, 2);
lean_inc(v_buildTime_814_);
lean_dec_ref(v___y_809_);
v___x_815_ = l_Lake_Log_maxLv(v_log_810_);
v___x_816_ = lean_array_get_size(v_log_810_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_nat_dec_eq(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = 1;
v___y_796_ = v___x_815_;
v___y_797_ = v_canceled_813_;
v___y_798_ = v___x_816_;
v___y_799_ = v_action_811_;
v___y_800_ = v_wantsRebuild_812_;
v___y_801_ = v___x_817_;
v___y_802_ = v_log_810_;
v___y_803_ = v_buildTime_814_;
v___y_804_ = v___x_819_;
goto v___jp_795_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = 0;
v___y_796_ = v___x_815_;
v___y_797_ = v_canceled_813_;
v___y_798_ = v___x_816_;
v___y_799_ = v_action_811_;
v___y_800_ = v_wantsRebuild_812_;
v___y_801_ = v___x_817_;
v___y_802_ = v_log_810_;
v___y_803_ = v_buildTime_814_;
v___y_804_ = v___x_820_;
goto v___jp_795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_823_, v_a_824_, v_a_825_);
lean_dec_ref(v_a_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_828_, uint8_t v___y_829_, uint8_t v_useAnsi_830_, lean_object* v_as_831_, size_t v_i_832_, size_t v_stop_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_828_, v___y_829_, v_useAnsi_830_, v_as_831_, v_i_832_, v_stop_833_, v_b_834_, v___y_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_839_, lean_object* v___y_840_, lean_object* v_useAnsi_841_, lean_object* v_as_842_, lean_object* v_i_843_, lean_object* v_stop_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v___y_15072__boxed_849_; uint8_t v_useAnsi_15073__boxed_850_; size_t v_i_boxed_851_; size_t v_stop_boxed_852_; lean_object* v_res_853_; 
v___y_15072__boxed_849_ = lean_unbox(v___y_840_);
v_useAnsi_15073__boxed_850_ = lean_unbox(v_useAnsi_841_);
v_i_boxed_851_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_stop_boxed_852_ = lean_unbox_usize(v_stop_844_);
lean_dec(v_stop_844_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_839_, v___y_15072__boxed_849_, v_useAnsi_15073__boxed_850_, v_as_842_, v_i_boxed_851_, v_stop_boxed_852_, v_b_845_, v___y_846_, v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_as_842_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_jobs_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_jobNo_863_; lean_object* v_totalJobs_864_; uint8_t v_wantsRebuild_865_; lean_object* v_failures_866_; lean_object* v_resetCtrl_867_; lean_object* v_lastUpdate_868_; lean_object* v_spinnerIdx_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_879_; 
v_jobs_859_ = lean_ctor_get(v_a_856_, 0);
v___x_860_ = lean_st_ref_take(v_jobs_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_862_ = lean_st_ref_put(v_jobs_859_, v___x_861_);
v_jobNo_863_ = lean_ctor_get(v_a_857_, 0);
v_totalJobs_864_ = lean_ctor_get(v_a_857_, 1);
v_wantsRebuild_865_ = lean_ctor_get_uint8(v_a_857_, sizeof(void*)*6);
v_failures_866_ = lean_ctor_get(v_a_857_, 2);
v_resetCtrl_867_ = lean_ctor_get(v_a_857_, 3);
v_lastUpdate_868_ = lean_ctor_get(v_a_857_, 4);
v_spinnerIdx_869_ = lean_ctor_get(v_a_857_, 5);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_857_);
if (v_isSharedCheck_879_ == 0)
{
v___x_871_ = v_a_857_;
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_spinnerIdx_869_);
lean_inc(v_lastUpdate_868_);
lean_inc(v_resetCtrl_867_);
lean_inc(v_failures_866_);
lean_inc(v_totalJobs_864_);
lean_inc(v_jobNo_863_);
lean_dec(v_a_857_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = lean_array_get_size(v___x_860_);
v___x_874_ = lean_nat_add(v_totalJobs_864_, v___x_873_);
lean_dec(v_totalJobs_864_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_jobNo_863_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_failures_866_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_resetCtrl_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_lastUpdate_868_);
lean_ctor_set(v_reuseFailAlloc_878_, 5, v_spinnerIdx_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_878_, sizeof(void*)*6, v_wantsRebuild_865_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_860_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_880_, v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object* v_as_884_, size_t v_i_885_, size_t v_stop_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_fst_892_; lean_object* v_snd_893_; uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_eq(v_i_885_, v_stop_886_);
if (v___x_897_ == 0)
{
lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_900_; lean_object* v_task_901_; uint8_t v___x_902_; 
v_fst_898_ = lean_ctor_get(v_b_887_, 0);
v_snd_899_ = lean_ctor_get(v_b_887_, 1);
v___x_900_ = lean_array_uget_borrowed(v_as_884_, v_i_885_);
v_task_901_ = lean_ctor_get(v___x_900_, 0);
v___x_902_ = lean_io_get_task_state(v_task_901_);
switch(v___x_902_)
{
case 0:
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_910_; 
lean_inc(v_snd_899_);
lean_inc(v_fst_898_);
v_isSharedCheck_910_ = !lean_is_exclusive(v_b_887_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_911_ = lean_ctor_get(v_b_887_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_b_887_, 0);
lean_dec(v_unused_912_);
v___x_904_ = v_b_887_;
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_b_887_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
lean_inc(v___x_900_);
v___x_906_ = lean_array_push(v_snd_899_, v___x_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_fst_898_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
v_fst_892_ = v___x_908_;
v_snd_893_ = v___y_889_;
goto v___jp_891_;
}
}
}
case 1:
{
lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
lean_inc(v_snd_899_);
lean_inc(v_fst_898_);
v_isSharedCheck_921_ = !lean_is_exclusive(v_b_887_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; lean_object* v_unused_923_; 
v_unused_922_ = lean_ctor_get(v_b_887_, 1);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_b_887_, 0);
lean_dec(v_unused_923_);
v___x_914_ = v_b_887_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_dec(v_b_887_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
lean_inc_n(v___x_900_, 2);
v___x_916_ = lean_array_push(v_fst_898_, v___x_900_);
v___x_917_ = lean_array_push(v_snd_899_, v___x_900_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_917_);
lean_ctor_set(v___x_914_, 0, v___x_916_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
v_fst_892_ = v___x_919_;
v_snd_893_ = v___y_889_;
goto v___jp_891_;
}
}
}
default: 
{
lean_object* v___x_924_; lean_object* v_snd_925_; lean_object* v_jobNo_926_; lean_object* v_totalJobs_927_; uint8_t v_wantsRebuild_928_; lean_object* v_failures_929_; lean_object* v_resetCtrl_930_; lean_object* v_lastUpdate_931_; lean_object* v_spinnerIdx_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_941_; 
lean_inc(v___x_900_);
v___x_924_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_900_, v___y_888_, v___y_889_);
v_snd_925_ = lean_ctor_get(v___x_924_, 1);
lean_inc(v_snd_925_);
lean_dec_ref(v___x_924_);
v_jobNo_926_ = lean_ctor_get(v_snd_925_, 0);
v_totalJobs_927_ = lean_ctor_get(v_snd_925_, 1);
v_wantsRebuild_928_ = lean_ctor_get_uint8(v_snd_925_, sizeof(void*)*6);
v_failures_929_ = lean_ctor_get(v_snd_925_, 2);
v_resetCtrl_930_ = lean_ctor_get(v_snd_925_, 3);
v_lastUpdate_931_ = lean_ctor_get(v_snd_925_, 4);
v_spinnerIdx_932_ = lean_ctor_get(v_snd_925_, 5);
v_isSharedCheck_941_ = !lean_is_exclusive(v_snd_925_);
if (v_isSharedCheck_941_ == 0)
{
v___x_934_ = v_snd_925_;
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_spinnerIdx_932_);
lean_inc(v_lastUpdate_931_);
lean_inc(v_resetCtrl_930_);
lean_inc(v_failures_929_);
lean_inc(v_totalJobs_927_);
lean_inc(v_jobNo_926_);
lean_dec(v_snd_925_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_941_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_jobNo_926_, v___x_936_);
lean_dec(v_jobNo_926_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_937_);
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_totalJobs_927_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_failures_929_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_resetCtrl_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_lastUpdate_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 5, v_spinnerIdx_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*6, v_wantsRebuild_928_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
v_fst_892_ = v_b_887_;
v_snd_893_ = v___x_939_;
goto v___jp_891_;
}
}
}
}
}
else
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_b_887_);
lean_ctor_set(v___x_942_, 1, v___y_889_);
return v___x_942_;
}
v___jp_891_:
{
size_t v___x_894_; size_t v___x_895_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_885_, v___x_894_);
v_i_885_ = v___x_895_;
v_b_887_ = v_fst_892_;
v___y_889_ = v_snd_893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object* v_as_943_, lean_object* v_i_944_, lean_object* v_stop_945_, lean_object* v_b_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
size_t v_i_boxed_950_; size_t v_stop_boxed_951_; lean_object* v_res_952_; 
v_i_boxed_950_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_stop_boxed_951_ = lean_unbox_usize(v_stop_945_);
lean_dec(v_stop_945_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_943_, v_i_boxed_950_, v_stop_boxed_951_, v_b_946_, v___y_947_, v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v_as_943_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object* v_new_955_, lean_object* v_unfinished_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v_fst_963_; lean_object* v_snd_964_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_970_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_971_ = lean_array_get_size(v_unfinished_956_);
v___x_972_ = lean_nat_dec_lt(v___x_960_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_inc_ref(v_a_958_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_970_);
lean_ctor_set(v___x_973_, 1, v_a_958_);
v___y_962_ = v___x_973_;
v_fst_963_ = v___x_970_;
v_snd_964_ = v_a_958_;
goto v___jp_961_;
}
else
{
size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; 
v___x_974_ = ((size_t)0ULL);
v___x_975_ = lean_usize_of_nat(v___x_971_);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_956_, v___x_974_, v___x_975_, v___x_970_, v_a_957_, v_a_958_);
v_fst_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_977_);
v_snd_978_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_snd_978_);
v___y_962_ = v___x_976_;
v_fst_963_ = v_fst_977_;
v_snd_964_ = v_snd_978_;
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = lean_array_get_size(v_new_955_);
v___x_966_ = lean_nat_dec_lt(v___x_960_, v___x_965_);
if (v___x_966_ == 0)
{
lean_dec_ref(v_snd_964_);
lean_dec_ref(v_fst_963_);
return v___y_962_;
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; 
lean_dec_ref(v___y_962_);
v___x_967_ = ((size_t)0ULL);
v___x_968_ = lean_usize_of_nat(v___x_965_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_955_, v___x_967_, v___x_968_, v_fst_963_, v_a_957_, v_snd_964_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_979_, lean_object* v_unfinished_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_979_, v_unfinished_980_, v_a_981_, v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec_ref(v_unfinished_980_);
lean_dec_ref(v_new_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___y_989_; lean_object* v___x_1007_; lean_object* v_lastUpdate_1008_; lean_object* v_updateFrequency_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1007_ = lean_io_mono_ms_now();
v_lastUpdate_1008_ = lean_ctor_get(v_a_986_, 4);
v_updateFrequency_1009_ = lean_ctor_get(v_a_985_, 2);
v___x_1010_ = lean_nat_sub(v___x_1007_, v_lastUpdate_1008_);
lean_dec(v___x_1007_);
v___x_1011_ = lean_nat_sub(v_updateFrequency_1009_, v___x_1010_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_nat_dec_lt(v___x_1012_, v___x_1011_);
if (v___x_1013_ == 0)
{
lean_dec(v___x_1011_);
v___y_989_ = v_a_986_;
goto v___jp_988_;
}
else
{
uint32_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_uint32_of_nat(v___x_1011_);
lean_dec(v___x_1011_);
v___x_1015_ = l_IO_sleep(v___x_1014_);
v___y_989_ = v_a_986_;
goto v___jp_988_;
}
v___jp_988_:
{
lean_object* v___x_990_; lean_object* v_jobNo_991_; lean_object* v_totalJobs_992_; uint8_t v_wantsRebuild_993_; lean_object* v_failures_994_; lean_object* v_resetCtrl_995_; lean_object* v_spinnerIdx_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1005_; 
v___x_990_ = lean_io_mono_ms_now();
v_jobNo_991_ = lean_ctor_get(v___y_989_, 0);
v_totalJobs_992_ = lean_ctor_get(v___y_989_, 1);
v_wantsRebuild_993_ = lean_ctor_get_uint8(v___y_989_, sizeof(void*)*6);
v_failures_994_ = lean_ctor_get(v___y_989_, 2);
v_resetCtrl_995_ = lean_ctor_get(v___y_989_, 3);
v_spinnerIdx_996_ = lean_ctor_get(v___y_989_, 5);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___y_989_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___y_989_, 4);
lean_dec(v_unused_1006_);
v___x_998_ = v___y_989_;
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_spinnerIdx_996_);
lean_inc(v_resetCtrl_995_);
lean_inc(v_failures_994_);
lean_inc(v_totalJobs_992_);
lean_inc(v_jobNo_991_);
lean_dec(v___y_989_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(0);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 4, v___x_990_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_jobNo_991_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_totalJobs_992_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_failures_994_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_resetCtrl_995_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_1004_, 5, v_spinnerIdx_996_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*6, v_wantsRebuild_993_);
v___x_1002_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1000_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1016_, v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_1020_, lean_object* v_unfinished_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v_failFast_1058_; 
v___x_1025_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1020_, v_unfinished_1021_, v_a_1022_, v_a_1023_);
lean_dec_ref(v_unfinished_1021_);
lean_dec_ref(v_new_1020_);
v_fst_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_snd_1027_);
lean_dec_ref(v___x_1025_);
v_fst_1028_ = lean_ctor_get(v_fst_1026_, 0);
lean_inc(v_fst_1028_);
v_snd_1029_ = lean_ctor_get(v_fst_1026_, 1);
lean_inc(v_snd_1029_);
lean_dec(v_fst_1026_);
v_failFast_1058_ = lean_ctor_get_uint8(v_a_1022_, sizeof(void*)*4 + 7);
if (v_failFast_1058_ == 0)
{
v___y_1031_ = v_a_1022_;
v___y_1032_ = v_snd_1027_;
goto v___jp_1030_;
}
else
{
lean_object* v_cancelTk_x3f_1059_; 
v_cancelTk_x3f_1059_ = lean_ctor_get(v_a_1022_, 3);
if (lean_obj_tag(v_cancelTk_x3f_1059_) == 1)
{
lean_object* v_val_1060_; lean_object* v_failures_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_val_1060_ = lean_ctor_get(v_cancelTk_x3f_1059_, 0);
v_failures_1061_ = lean_ctor_get(v_snd_1027_, 2);
v___x_1062_ = lean_array_get_size(v_failures_1061_);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_nat_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = l_IO_CancelToken_set(v_val_1060_);
v___y_1031_ = v_a_1022_;
v___y_1032_ = v_snd_1027_;
goto v___jp_1030_;
}
else
{
v___y_1031_ = v_a_1022_;
v___y_1032_ = v_snd_1027_;
goto v___jp_1030_;
}
}
else
{
v___y_1031_ = v_a_1022_;
v___y_1032_ = v_snd_1027_;
goto v___jp_1030_;
}
}
v___jp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_array_get_size(v_snd_1029_);
v___x_1035_ = lean_nat_dec_lt(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_fst_1028_);
v___x_1036_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1031_, v___y_1032_);
v_fst_1037_ = lean_ctor_get(v___x_1036_, 0);
v_snd_1038_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_array_get_size(v_fst_1037_);
v___x_1043_ = lean_nat_dec_lt(v___x_1033_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec(v_fst_1037_);
lean_dec(v_snd_1029_);
v___x_1044_ = lean_box(0);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_snd_1038_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_del_object(v___x_1040_);
v_new_1020_ = v_fst_1037_;
v_unfinished_1021_ = v_snd_1029_;
v_a_1022_ = v___y_1031_;
v_a_1023_ = v_snd_1038_;
goto _start;
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v_snd_1051_; lean_object* v___x_1052_; lean_object* v_snd_1053_; lean_object* v___x_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; 
v___x_1050_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1028_, v_snd_1029_, v___y_1031_, v___y_1032_);
lean_dec(v_fst_1028_);
v_snd_1051_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_snd_1051_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v___y_1031_, v_snd_1051_);
v_snd_1053_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_snd_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1031_, v_snd_1053_);
v_fst_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1054_);
v_new_1020_ = v_fst_1055_;
v_unfinished_1021_ = v_snd_1029_;
v_a_1022_ = v___y_1031_;
v_a_1023_ = v_snd_1056_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1066_, lean_object* v_unfinished_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1066_, v_unfinished_1067_, v_a_1068_, v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1147_; 
v___x_1076_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1073_, v_a_1074_);
v_fst_1077_ = lean_ctor_get(v___x_1076_, 0);
v_snd_1078_ = lean_ctor_get(v___x_1076_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1080_ = v___x_1076_;
v_isShared_1081_ = v_isSharedCheck_1147_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_inc(v_fst_1077_);
lean_dec(v___x_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1147_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v_snd_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1145_; 
v___x_1082_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1077_, v_init_1072_, v_a_1073_, v_snd_1078_);
v_snd_1083_ = lean_ctor_get(v___x_1082_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1082_, 0);
lean_dec(v_unused_1146_);
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1145_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_snd_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1145_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_jobNo_1087_; lean_object* v_totalJobs_1088_; uint8_t v_wantsRebuild_1089_; lean_object* v_failures_1090_; lean_object* v_resetCtrl_1091_; lean_object* v_lastUpdate_1092_; lean_object* v_spinnerIdx_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1144_; 
v_jobNo_1087_ = lean_ctor_get(v_snd_1083_, 0);
v_totalJobs_1088_ = lean_ctor_get(v_snd_1083_, 1);
v_wantsRebuild_1089_ = lean_ctor_get_uint8(v_snd_1083_, sizeof(void*)*6);
v_failures_1090_ = lean_ctor_get(v_snd_1083_, 2);
v_resetCtrl_1091_ = lean_ctor_get(v_snd_1083_, 3);
v_lastUpdate_1092_ = lean_ctor_get(v_snd_1083_, 4);
v_spinnerIdx_1093_ = lean_ctor_get(v_snd_1083_, 5);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_snd_1083_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1095_ = v_snd_1083_;
v_isShared_1096_ = v_isSharedCheck_1144_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_spinnerIdx_1093_);
lean_inc(v_lastUpdate_1092_);
lean_inc(v_resetCtrl_1091_);
lean_inc(v_failures_1090_);
lean_inc(v_totalJobs_1088_);
lean_inc(v_jobNo_1087_);
lean_dec(v_snd_1083_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1144_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 3, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_jobNo_1087_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_totalJobs_1088_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_failures_1090_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_lastUpdate_1092_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_spinnerIdx_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*6, v_wantsRebuild_1089_);
v___x_1099_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v_val_1101_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = lean_string_utf8_byte_size(v_resetCtrl_1091_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_nat_dec_eq(v___x_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v_out_1108_; lean_object* v_flush_1109_; lean_object* v_putStr_1110_; lean_object* v___x_1115_; 
lean_del_object(v___x_1080_);
v_out_1108_ = lean_ctor_get(v_a_1073_, 1);
v_flush_1109_ = lean_ctor_get(v_out_1108_, 0);
v_putStr_1110_ = lean_ctor_get(v_out_1108_, 4);
lean_inc_ref(v_putStr_1110_);
lean_inc_ref(v_resetCtrl_1091_);
v___x_1115_ = lean_apply_2(v_putStr_1110_, v_resetCtrl_1091_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec_ref_known(v___x_1115_, 1);
lean_dec_ref(v_resetCtrl_1091_);
goto v___jp_1111_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1138_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1138_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1138_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1120_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1121_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1122_ = lean_unsigned_to_nat(82u);
v___x_1123_ = lean_unsigned_to_nat(4u);
v___x_1124_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1125_ = lean_io_error_to_string(v_a_1116_);
v___x_1126_ = lean_string_append(v___x_1124_, v___x_1125_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1128_ = lean_string_append(v___x_1126_, v___x_1127_);
v___x_1129_ = l_String_quote(v_resetCtrl_1091_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 3);
lean_ctor_set(v___x_1118_, 0, v___x_1129_);
v___x_1131_ = v___x_1118_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1132_ = l_Std_Format_defWidth;
v___x_1133_ = l_Std_Format_pretty(v___x_1131_, v___x_1132_, v___x_1106_, v___x_1106_);
v___x_1134_ = lean_string_append(v___x_1128_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = l_mkPanicMessageWithDecl(v___x_1120_, v___x_1121_, v___x_1122_, v___x_1123_, v___x_1134_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1135_);
goto v___jp_1111_;
}
}
}
v___jp_1111_:
{
lean_object* v___x_1112_; 
lean_inc_ref(v_flush_1109_);
v___x_1112_ = lean_apply_1(v_flush_1109_, lean_box(0));
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v_val_1101_ = v_a_1113_;
goto v___jp_1100_;
}
else
{
lean_object* v___x_1114_; 
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = lean_box(0);
v_val_1101_ = v___x_1114_;
goto v___jp_1100_;
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_dec_ref(v_resetCtrl_1091_);
lean_del_object(v___x_1085_);
v___x_1139_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1099_);
lean_ctor_set(v___x_1080_, 0, v___x_1139_);
v___x_1141_ = v___x_1080_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1099_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
v___jp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v___x_1099_);
lean_ctor_set(v___x_1085_, 0, v_val_1101_);
v___x_1103_ = v___x_1085_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_val_1101_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1099_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1148_, v_a_1149_, v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1153_){
_start:
{
lean_object* v_failures_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_failures_1154_ = lean_ctor_get(v_self_1153_, 0);
v___x_1155_ = lean_array_get_size(v_failures_1154_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_nat_dec_eq(v___x_1155_, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1158_);
lean_dec_ref(v_self_1158_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1161_, lean_object* v_jobs_1162_, lean_object* v_cancelTk_x3f_1163_){
_start:
{
lean_object* v_toLogConfig_1165_; uint8_t v_failFast_1166_; uint8_t v_verbosity_1167_; uint8_t v_failLv_1168_; uint8_t v_outLv_1169_; uint8_t v_ansiMode_1170_; lean_object* v_out_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; uint8_t v___y_1180_; uint8_t v___y_1181_; uint8_t v___y_1185_; 
v_toLogConfig_1165_ = lean_ctor_get(v_cfg_1161_, 0);
v_failFast_1166_ = lean_ctor_get_uint8(v_cfg_1161_, sizeof(void*)*5 + 3);
v_verbosity_1167_ = lean_ctor_get_uint8(v_cfg_1161_, sizeof(void*)*5 + 4);
v_failLv_1168_ = lean_ctor_get_uint8(v_toLogConfig_1165_, sizeof(void*)*1);
v_outLv_1169_ = lean_ctor_get_uint8(v_toLogConfig_1165_, sizeof(void*)*1 + 1);
v_ansiMode_1170_ = lean_ctor_get_uint8(v_toLogConfig_1165_, sizeof(void*)*1 + 2);
v_out_1171_ = lean_ctor_get(v_toLogConfig_1165_, 0);
v___x_1172_ = l_Lake_OutStream_get(v_out_1171_);
lean_inc_ref(v___x_1172_);
v___x_1173_ = l_Lake_AnsiMode_isEnabled(v___x_1172_, v_ansiMode_1170_);
v___x_1174_ = l_Lake_BuildConfig_showProgress(v_cfg_1161_);
v___x_1175_ = lean_box(v_verbosity_1167_);
v___x_1176_ = lean_obj_tag_nat(v___x_1175_);
lean_dec(v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(2u);
v___x_1178_ = lean_nat_dec_eq(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = 3;
v___y_1185_ = v___x_1187_;
goto v___jp_1184_;
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = 0;
v___y_1185_ = v___x_1188_;
goto v___jp_1184_;
}
v___jp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_unsigned_to_nat(100u);
v___x_1183_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_1183_, 0, v_jobs_1162_);
lean_ctor_set(v___x_1183_, 1, v___x_1172_);
lean_ctor_set(v___x_1183_, 2, v___x_1182_);
lean_ctor_set(v___x_1183_, 3, v_cancelTk_x3f_1163_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4, v_outLv_1169_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 1, v_failLv_1168_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 2, v___y_1180_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 3, v___x_1178_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 4, v___x_1173_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 5, v___x_1174_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 6, v___y_1181_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*4 + 7, v_failFast_1166_);
return v___x_1183_;
}
v___jp_1184_:
{
if (v___x_1178_ == 0)
{
if (v___x_1173_ == 0)
{
uint8_t v___x_1186_; 
v___x_1186_ = 1;
v___y_1180_ = v___y_1185_;
v___y_1181_ = v___x_1186_;
goto v___jp_1179_;
}
else
{
v___y_1180_ = v___y_1185_;
v___y_1181_ = v___x_1178_;
goto v___jp_1179_;
}
}
else
{
v___y_1180_ = v___y_1185_;
v___y_1181_ = v___x_1178_;
goto v___jp_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1189_, lean_object* v_jobs_1190_, lean_object* v_cancelTk_x3f_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1189_, v_jobs_1190_, v_cancelTk_x3f_1191_);
lean_dec_ref(v_cfg_1189_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1194_, lean_object* v_initJobs_1195_, lean_object* v_initFailures_1196_, lean_object* v_resetCtrl_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_snd_1204_; lean_object* v_totalJobs_1205_; uint8_t v_wantsRebuild_1206_; lean_object* v_failures_1207_; lean_object* v___x_1208_; 
v___x_1199_ = lean_io_mono_ms_now();
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = 0;
v___x_1202_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
lean_ctor_set(v___x_1202_, 2, v_initFailures_1196_);
lean_ctor_set(v___x_1202_, 3, v_resetCtrl_1197_);
lean_ctor_set(v___x_1202_, 4, v___x_1199_);
lean_ctor_set(v___x_1202_, 5, v___x_1200_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*6, v___x_1201_);
v___x_1203_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1195_, v_ctx_1194_, v___x_1202_);
v_snd_1204_ = lean_ctor_get(v___x_1203_, 1);
lean_inc(v_snd_1204_);
lean_dec_ref(v___x_1203_);
v_totalJobs_1205_ = lean_ctor_get(v_snd_1204_, 1);
lean_inc(v_totalJobs_1205_);
v_wantsRebuild_1206_ = lean_ctor_get_uint8(v_snd_1204_, sizeof(void*)*6);
v_failures_1207_ = lean_ctor_get(v_snd_1204_, 2);
lean_inc_ref(v_failures_1207_);
lean_dec(v_snd_1204_);
v___x_1208_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1208_, 0, v_failures_1207_);
lean_ctor_set(v___x_1208_, 1, v_totalJobs_1205_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*2, v_wantsRebuild_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1209_, lean_object* v_initJobs_1210_, lean_object* v_initFailures_1211_, lean_object* v_resetCtrl_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1209_, v_initJobs_1210_, v_initFailures_1211_, v_resetCtrl_1212_);
lean_dec_ref(v_ctx_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1215_, lean_object* v_jobs_1216_, lean_object* v_out_1217_, uint8_t v_failLv_1218_, uint8_t v_outLv_1219_, uint8_t v_minAction_1220_, uint8_t v_showOptional_1221_, uint8_t v_useAnsi_1222_, uint8_t v_showProgress_1223_, uint8_t v_showTime_1224_, lean_object* v_resetCtrl_1225_, lean_object* v_initFailures_1226_, lean_object* v_updateFrequency_1227_){
_start:
{
uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v_ctx_1231_; lean_object* v___x_1232_; 
v___x_1229_ = 0;
v___x_1230_ = lean_box(0);
v_ctx_1231_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_ctx_1231_, 0, v_jobs_1216_);
lean_ctor_set(v_ctx_1231_, 1, v_out_1217_);
lean_ctor_set(v_ctx_1231_, 2, v_updateFrequency_1227_);
lean_ctor_set(v_ctx_1231_, 3, v___x_1230_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4, v_outLv_1219_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 1, v_failLv_1218_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 2, v_minAction_1220_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 3, v_showOptional_1221_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 4, v_useAnsi_1222_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 5, v_showProgress_1223_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 6, v_showTime_1224_);
lean_ctor_set_uint8(v_ctx_1231_, sizeof(void*)*4 + 7, v___x_1229_);
v___x_1232_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1231_, v_initJobs_1215_, v_initFailures_1226_, v_resetCtrl_1225_);
lean_dec_ref_known(v_ctx_1231_, 4);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(lean_object* v_logger_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_apply_2(v_logger_1256_, v___y_1258_, lean_box(0));
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed(lean_object* v_logger_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(v_logger_1261_, v_x_1262_, v___y_1263_);
return v_res_1265_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1268_ = l_String_quote(v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1);
v___x_1270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = l_Std_Format_defWidth;
v___x_1273_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2);
v___x_1274_ = l_Std_Format_pretty(v___x_1273_, v___x_1272_, v___x_1271_, v___x_1271_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1282_ = l_String_quote(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8);
v___x_1284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = l_Std_Format_defWidth;
v___x_1287_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9);
v___x_1288_ = l_Std_Format_pretty(v___x_1287_, v___x_1286_, v___x_1285_, v___x_1285_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1291_ = l_String_quote(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12);
v___x_1293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = l_Std_Format_defWidth;
v___x_1296_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13);
v___x_1297_ = l_Std_Format_pretty(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1294_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1301_ = l_String_quote(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17);
v___x_1303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = l_Std_Format_defWidth;
v___x_1306_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18);
v___x_1307_ = l_Std_Format_pretty(v___x_1306_, v___x_1305_, v___x_1304_, v___x_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(lean_object* v_logger_1308_, lean_object* v_bctx_1309_, lean_object* v_out_1310_, lean_object* v_outputsFile_1311_){
_start:
{
lean_object* v___x_1319_; lean_object* v_outputsRef_x3f_1320_; 
v___x_1319_ = l_instMonadBaseIO;
v_outputsRef_x3f_1320_ = lean_ctor_get(v_bctx_1309_, 5);
lean_inc(v_outputsRef_x3f_1320_);
if (lean_obj_tag(v_outputsRef_x3f_1320_) == 1)
{
lean_object* v_toContext_1321_; lean_object* v_toBuildConfig_1322_; lean_object* v_val_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1469_; 
v_toContext_1321_ = lean_ctor_get(v_bctx_1309_, 1);
lean_inc(v_toContext_1321_);
v_toBuildConfig_1322_ = lean_ctor_get(v_bctx_1309_, 0);
lean_inc_ref(v_toBuildConfig_1322_);
lean_dec_ref(v_bctx_1309_);
v_val_1323_ = lean_ctor_get(v_outputsRef_x3f_1320_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_outputsRef_x3f_1320_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1325_ = v_outputsRef_x3f_1320_;
v_isShared_1326_ = v_isSharedCheck_1469_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_val_1323_);
lean_dec(v_outputsRef_x3f_1320_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1469_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_lakeEnv_1327_; lean_object* v_packages_1328_; uint8_t v_verbosity_1329_; lean_object* v_outputsIdx_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_lakeEnv_1327_ = lean_ctor_get(v_toContext_1321_, 0);
lean_inc_ref(v_lakeEnv_1327_);
v_packages_1328_ = lean_ctor_get(v_toContext_1321_, 4);
lean_inc_ref(v_packages_1328_);
lean_dec(v_toContext_1321_);
v_verbosity_1329_ = lean_ctor_get_uint8(v_toBuildConfig_1322_, sizeof(void*)*5 + 4);
v_outputsIdx_1330_ = lean_ctor_get(v_toBuildConfig_1322_, 2);
lean_inc(v_outputsIdx_1330_);
lean_dec_ref(v_toBuildConfig_1322_);
v___x_1331_ = lean_array_get_size(v_packages_1328_);
v___x_1332_ = lean_nat_dec_lt(v_outputsIdx_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v_putStr_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_outputsIdx_1330_);
lean_dec_ref(v_packages_1328_);
lean_dec_ref(v_lakeEnv_1327_);
lean_del_object(v___x_1325_);
lean_dec(v_val_1323_);
lean_dec_ref(v_outputsFile_1311_);
lean_dec_ref(v_logger_1308_);
v_putStr_1333_ = lean_ctor_get(v_out_1310_, 4);
lean_inc_ref(v_putStr_1333_);
lean_dec_ref(v_out_1310_);
v___x_1334_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1335_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1336_ = lean_apply_2(v_putStr_1333_, v___x_1334_, lean_box(0));
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_dec_ref_known(v___x_1336_, 1);
goto v___jp_1315_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_2543__overap_1350_; lean_object* v___x_1351_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1339_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1340_ = lean_unsigned_to_nat(82u);
v___x_1341_ = lean_unsigned_to_nat(4u);
v___x_1342_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1343_ = lean_io_error_to_string(v_a_1337_);
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
v___x_1349_ = l_mkPanicMessageWithDecl(v___x_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v___x_1348_);
lean_dec_ref(v___x_1348_);
v___x_2543__overap_1350_ = l_panic___redArg(v___x_1335_, v___x_1349_);
v___x_1351_ = lean_apply_1(v___x_2543__overap_1350_, lean_box(0));
lean_dec(v___x_1351_);
goto v___jp_1315_;
}
}
else
{
lean_object* v___x_1352_; lean_object* v_config_1353_; lean_object* v_baseName_1354_; lean_object* v_toLeanConfig_1355_; lean_object* v_enableArtifactCache_x3f_1356_; lean_object* v___f_1357_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1381_; uint8_t v___y_1448_; uint8_t v___y_1456_; 
v___x_1352_ = lean_array_fget_borrowed(v_packages_1328_, v_outputsIdx_1330_);
lean_dec(v_outputsIdx_1330_);
v_config_1353_ = lean_ctor_get(v___x_1352_, 6);
v_baseName_1354_ = lean_ctor_get(v___x_1352_, 1);
lean_inc(v_baseName_1354_);
v_toLeanConfig_1355_ = lean_ctor_get(v_config_1353_, 1);
lean_inc_ref(v_toLeanConfig_1355_);
v_enableArtifactCache_x3f_1356_ = lean_ctor_get(v_config_1353_, 24);
lean_inc_ref(v_logger_1308_);
v___f_1357_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1357_, 0, v_logger_1308_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1356_) == 0)
{
lean_object* v_enableArtifactCache_x3f_1457_; 
v_enableArtifactCache_x3f_1457_ = lean_ctor_get(v_lakeEnv_1327_, 6);
lean_inc(v_enableArtifactCache_x3f_1457_);
lean_dec_ref(v_lakeEnv_1327_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1457_) == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_config_1460_; lean_object* v_enableArtifactCache_x3f_1461_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_array_fget(v_packages_1328_, v___x_1458_);
lean_dec_ref(v_packages_1328_);
v_config_1460_ = lean_ctor_get(v___x_1459_, 6);
lean_inc_ref(v_config_1460_);
lean_dec(v___x_1459_);
v_enableArtifactCache_x3f_1461_ = lean_ctor_get(v_config_1460_, 24);
lean_inc(v_enableArtifactCache_x3f_1461_);
lean_dec_ref(v_config_1460_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1461_) == 0)
{
uint8_t v___x_1462_; 
v___x_1462_ = 0;
v___y_1448_ = v___x_1462_;
goto v___jp_1447_;
}
else
{
lean_object* v_val_1463_; uint8_t v___x_1464_; 
v_val_1463_ = lean_ctor_get(v_enableArtifactCache_x3f_1461_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1461_, 1);
v___x_1464_ = lean_unbox(v_val_1463_);
lean_dec(v_val_1463_);
v___y_1456_ = v___x_1464_;
goto v___jp_1455_;
}
}
else
{
lean_object* v_val_1465_; uint8_t v___x_1466_; 
lean_dec_ref(v_packages_1328_);
v_val_1465_ = lean_ctor_get(v_enableArtifactCache_x3f_1457_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1457_, 1);
v___x_1466_ = lean_unbox(v_val_1465_);
lean_dec(v_val_1465_);
v___y_1456_ = v___x_1466_;
goto v___jp_1455_;
}
}
else
{
lean_object* v_val_1467_; uint8_t v___x_1468_; 
lean_inc_ref(v_enableArtifactCache_x3f_1356_);
lean_dec_ref(v_packages_1328_);
lean_dec_ref(v_lakeEnv_1327_);
v_val_1467_ = lean_ctor_get(v_enableArtifactCache_x3f_1356_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1356_, 1);
v___x_1468_ = lean_unbox(v_val_1467_);
lean_dec(v_val_1467_);
v___y_1456_ = v___x_1468_;
goto v___jp_1455_;
}
v___jp_1358_:
{
if (v___y_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___f_1357_);
v___x_1362_ = lean_box(0);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_array_get_size(v___y_1360_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_nat_dec_lt(v___y_1359_, v___x_1363_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v___y_1360_);
lean_dec_ref(v___f_1357_);
return v___x_1364_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_2357__overap_1368_; lean_object* v___x_1369_; 
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = lean_usize_of_nat(v___x_1363_);
v___x_2357__overap_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1319_, v___f_1357_, v___y_1360_, v___x_1366_, v___x_1367_, v___x_1364_);
v___x_1369_ = lean_apply_1(v___x_2357__overap_1368_, lean_box(0));
return v___x_1369_;
}
}
}
v___jp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_array_get_size(v___y_1372_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_nat_dec_lt(v___y_1371_, v___x_1373_);
if (v___x_1375_ == 0)
{
lean_dec_ref(v___y_1372_);
lean_dec_ref(v___f_1357_);
return v___x_1374_;
}
else
{
size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_2287__overap_1378_; lean_object* v___x_1379_; 
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = lean_usize_of_nat(v___x_1373_);
v___x_2287__overap_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1319_, v___f_1357_, v___y_1372_, v___x_1376_, v___x_1377_, v___x_1374_);
v___x_1379_ = lean_apply_1(v___x_2287__overap_1378_, lean_box(0));
return v___x_1379_;
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; lean_object* v_platformIndependent_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1382_ = lean_st_ref_get(v_val_1323_);
lean_dec(v_val_1323_);
v_platformIndependent_1383_ = lean_ctor_get(v_toLeanConfig_1355_, 10);
lean_inc(v_platformIndependent_1383_);
lean_dec_ref(v_toLeanConfig_1355_);
v___f_1384_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5));
v___x_1385_ = lean_box(v___x_1332_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1385_);
v___x_1387_ = v___x_1325_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1388_ = l_instBEqOption_beq___redArg(v___f_1384_, v_platformIndependent_1383_, v___x_1387_);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_1391_ = l_Lake_CacheMap_writeFile(v_outputsFile_1311_, v___x_1382_, v___x_1388_, v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 2);
v___x_1393_ = lean_array_get_size(v_a_1392_);
v___x_1394_ = lean_nat_dec_eq(v___x_1393_, v___x_1389_);
if (v___x_1394_ == 0)
{
if (v___y_1381_ == 0)
{
lean_dec(v_a_1392_);
lean_dec_ref(v___f_1357_);
lean_dec_ref(v_out_1310_);
goto v___jp_1313_;
}
else
{
lean_object* v_putStr_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_putStr_1395_ = lean_ctor_get(v_out_1310_, 4);
lean_inc_ref(v_putStr_1395_);
lean_dec_ref(v_out_1310_);
v___x_1396_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1397_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1398_ = lean_apply_2(v_putStr_1395_, v___x_1396_, lean_box(0));
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_dec_ref_known(v___x_1398_, 1);
v___y_1371_ = v___x_1389_;
v___y_1372_ = v_a_1392_;
goto v___jp_1370_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_2551__overap_1417_; lean_object* v___x_1418_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v___x_1400_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1401_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1402_ = lean_unsigned_to_nat(82u);
v___x_1403_ = lean_unsigned_to_nat(4u);
v___x_1404_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1405_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1405_, v___y_1381_);
v___x_1407_ = lean_string_append(v___x_1404_, v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1409_ = lean_string_append(v___x_1407_, v___x_1408_);
v___x_1410_ = lean_io_error_to_string(v_a_1399_);
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_1415_ = lean_string_append(v___x_1413_, v___x_1414_);
v___x_1416_ = l_mkPanicMessageWithDecl(v___x_1400_, v___x_1401_, v___x_1402_, v___x_1403_, v___x_1415_);
lean_dec_ref(v___x_1415_);
v___x_2551__overap_1417_ = l_panic___redArg(v___x_1397_, v___x_1416_);
v___x_1418_ = lean_apply_1(v___x_2551__overap_1417_, lean_box(0));
lean_dec(v___x_1418_);
v___y_1371_ = v___x_1389_;
v___y_1372_ = v_a_1392_;
goto v___jp_1370_;
}
}
}
else
{
lean_dec(v_a_1392_);
lean_dec_ref(v___f_1357_);
lean_dec_ref(v_out_1310_);
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1419_; lean_object* v_putStr_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_a_1419_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1391_, 2);
v_putStr_1420_ = lean_ctor_get(v_out_1310_, 4);
lean_inc_ref(v_putStr_1420_);
lean_dec_ref(v_out_1310_);
v___x_1421_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1422_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1423_ = lean_apply_2(v_putStr_1420_, v___x_1421_, lean_box(0));
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_dec_ref_known(v___x_1423_, 1);
v___y_1359_ = v___x_1389_;
v___y_1360_ = v_a_1419_;
v___y_1361_ = v___y_1381_;
goto v___jp_1358_;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_2556__overap_1442_; lean_object* v___x_1443_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1426_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1427_ = lean_unsigned_to_nat(82u);
v___x_1428_ = lean_unsigned_to_nat(4u);
v___x_1429_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1430_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1430_, v___x_1332_);
v___x_1432_ = lean_string_append(v___x_1429_, v___x_1431_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1434_ = lean_string_append(v___x_1432_, v___x_1433_);
v___x_1435_ = lean_io_error_to_string(v_a_1424_);
v___x_1436_ = lean_string_append(v___x_1434_, v___x_1435_);
lean_dec_ref(v___x_1435_);
v___x_1437_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1438_ = lean_string_append(v___x_1436_, v___x_1437_);
v___x_1439_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_1440_ = lean_string_append(v___x_1438_, v___x_1439_);
v___x_1441_ = l_mkPanicMessageWithDecl(v___x_1425_, v___x_1426_, v___x_1427_, v___x_1428_, v___x_1440_);
lean_dec_ref(v___x_1440_);
v___x_2556__overap_1442_ = l_panic___redArg(v___x_1422_, v___x_1441_);
v___x_1443_ = lean_apply_1(v___x_2556__overap_1442_, lean_box(0));
lean_dec(v___x_1443_);
v___y_1359_ = v___x_1389_;
v___y_1360_ = v_a_1419_;
v___y_1361_ = v___y_1381_;
goto v___jp_1358_;
}
}
}
}
v___jp_1445_:
{
if (v_verbosity_1329_ == 2)
{
v___y_1381_ = v___x_1332_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1446_; 
v___x_1446_ = 0;
v___y_1381_ = v___x_1446_;
goto v___jp_1380_;
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = l_Lean_Name_toString(v_baseName_1354_, v___y_1448_);
v___x_1450_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_1451_ = lean_string_append(v___x_1449_, v___x_1450_);
v___x_1452_ = 2;
v___x_1453_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*1, v___x_1452_);
v___x_1454_ = lean_apply_2(v_logger_1308_, v___x_1453_, lean_box(0));
goto v___jp_1445_;
}
v___jp_1455_:
{
if (v___y_1456_ == 0)
{
v___y_1448_ = v___y_1456_;
goto v___jp_1447_;
}
else
{
lean_dec(v_baseName_1354_);
lean_dec_ref(v_logger_1308_);
goto v___jp_1445_;
}
}
}
}
}
else
{
lean_object* v_putStr_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_outputsRef_x3f_1320_);
lean_dec_ref(v_outputsFile_1311_);
lean_dec_ref(v_bctx_1309_);
lean_dec_ref(v_logger_1308_);
v_putStr_1470_ = lean_ctor_get(v_out_1310_, 4);
lean_inc_ref(v_putStr_1470_);
lean_dec_ref(v_out_1310_);
v___x_1471_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1472_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1473_ = lean_apply_2(v_putStr_1470_, v___x_1471_, lean_box(0));
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_dec_ref_known(v___x_1473_, 1);
goto v___jp_1317_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_2561__overap_1487_; lean_object* v___x_1488_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1476_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1477_ = lean_unsigned_to_nat(82u);
v___x_1478_ = lean_unsigned_to_nat(4u);
v___x_1479_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1480_ = lean_io_error_to_string(v_a_1474_);
v___x_1481_ = lean_string_append(v___x_1479_, v___x_1480_);
lean_dec_ref(v___x_1480_);
v___x_1482_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1483_ = lean_string_append(v___x_1481_, v___x_1482_);
v___x_1484_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_1485_ = lean_string_append(v___x_1483_, v___x_1484_);
v___x_1486_ = l_mkPanicMessageWithDecl(v___x_1475_, v___x_1476_, v___x_1477_, v___x_1478_, v___x_1485_);
lean_dec_ref(v___x_1485_);
v___x_2561__overap_1487_ = l_panic___redArg(v___x_1472_, v___x_1486_);
v___x_1488_ = lean_apply_1(v___x_2561__overap_1487_, lean_box(0));
lean_dec(v___x_1488_);
goto v___jp_1317_;
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
v___jp_1315_:
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
v___jp_1317_:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___boxed(lean_object* v_logger_1489_, lean_object* v_bctx_1490_, lean_object* v_out_1491_, lean_object* v_outputsFile_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(v_logger_1489_, v_bctx_1490_, v_out_1491_, v_outputsFile_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1496_, lean_object* v_as_1497_, size_t v_i_1498_, size_t v_stop_1499_, lean_object* v_b_1500_){
_start:
{
lean_object* v_val_1503_; uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_eq(v_i_1498_, v_stop_1499_);
if (v___x_1507_ == 0)
{
lean_object* v_putStr_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_putStr_1508_ = lean_ctor_get(v_out_1496_, 4);
v___x_1509_ = lean_array_uget_borrowed(v_as_1497_, v_i_1498_);
v___x_1510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1511_ = lean_string_append(v___x_1510_, v___x_1509_);
v___x_1512_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1513_ = lean_string_append(v___x_1511_, v___x_1512_);
lean_inc_ref(v_putStr_1508_);
lean_inc_ref(v___x_1513_);
v___x_1514_ = lean_apply_2(v_putStr_1508_, v___x_1513_, lean_box(0));
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; 
lean_dec_ref(v___x_1513_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v_val_1503_ = v_a_1515_;
goto v___jp_1502_;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1539_; 
v_a_1516_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1518_ = v___x_1514_;
v_isShared_1519_ = v_isSharedCheck_1539_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1539_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1520_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1521_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1522_ = lean_unsigned_to_nat(82u);
v___x_1523_ = lean_unsigned_to_nat(4u);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1526_ = lean_io_error_to_string(v_a_1516_);
v___x_1527_ = lean_string_append(v___x_1525_, v___x_1526_);
lean_dec_ref(v___x_1526_);
v___x_1528_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
v___x_1530_ = l_String_quote(v___x_1513_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 3);
lean_ctor_set(v___x_1518_, 0, v___x_1530_);
v___x_1532_ = v___x_1518_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1533_ = l_Std_Format_defWidth;
v___x_1534_ = l_Std_Format_pretty(v___x_1532_, v___x_1533_, v___x_1524_, v___x_1524_);
v___x_1535_ = lean_string_append(v___x_1529_, v___x_1534_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = l_mkPanicMessageWithDecl(v___x_1520_, v___x_1521_, v___x_1522_, v___x_1523_, v___x_1535_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1536_);
v_val_1503_ = v___x_1537_;
goto v___jp_1502_;
}
}
}
}
else
{
lean_dec_ref(v_out_1496_);
return v_b_1500_;
}
v___jp_1502_:
{
size_t v___x_1504_; size_t v___x_1505_; 
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1498_, v___x_1504_);
v_i_1498_ = v___x_1505_;
v_b_1500_ = v_val_1503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1540_, lean_object* v_as_1541_, lean_object* v_i_1542_, lean_object* v_stop_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_){
_start:
{
size_t v_i_boxed_1546_; size_t v_stop_boxed_1547_; lean_object* v_res_1548_; 
v_i_boxed_1546_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_stop_boxed_1547_ = lean_unbox_usize(v_stop_1543_);
lean_dec(v_stop_1543_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1540_, v_as_1541_, v_i_boxed_1546_, v_stop_boxed_1547_, v_b_1544_);
lean_dec_ref(v_as_1541_);
return v_res_1548_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1551_ = l_String_quote(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__2(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__1, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__1);
v___x_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__3(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = l_Std_Format_defWidth;
v___x_1556_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__2, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__2);
v___x_1557_ = l_Std_Format_pretty(v___x_1556_, v___x_1555_, v___x_1554_, v___x_1554_);
return v___x_1557_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1565_ = l_String_quote(v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = l_Std_Format_defWidth;
v___x_1570_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1571_ = l_Std_Format_pretty(v___x_1570_, v___x_1569_, v___x_1568_, v___x_1568_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1572_, lean_object* v_out_1573_, lean_object* v_result_1574_){
_start:
{
lean_object* v_failures_1578_; lean_object* v_numJobs_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_failures_1578_ = lean_ctor_get(v_result_1574_, 0);
lean_inc_ref(v_failures_1578_);
v_numJobs_1579_ = lean_ctor_get(v_result_1574_, 1);
lean_inc(v_numJobs_1579_);
lean_dec_ref(v_result_1574_);
v___x_1580_ = lean_array_get_size(v_failures_1578_);
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = lean_nat_dec_eq(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v_flush_1583_; lean_object* v_putStr_1584_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_numJobs_1579_);
v_flush_1583_ = lean_ctor_get(v_out_1573_, 0);
lean_inc_ref(v_flush_1583_);
v_putStr_1584_ = lean_ctor_get(v_out_1573_, 4);
v___x_1595_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
lean_inc_ref(v_putStr_1584_);
v___x_1596_ = lean_apply_2(v_putStr_1584_, v___x_1595_, lean_box(0));
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_dec_ref_known(v___x_1596_, 1);
goto v___jp_1589_;
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v___x_1598_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1599_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1600_ = lean_unsigned_to_nat(82u);
v___x_1601_ = lean_unsigned_to_nat(4u);
v___x_1602_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1603_ = lean_io_error_to_string(v_a_1597_);
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
v___x_1607_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__3, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__3);
v___x_1608_ = lean_string_append(v___x_1606_, v___x_1607_);
v___x_1609_ = l_mkPanicMessageWithDecl(v___x_1598_, v___x_1599_, v___x_1600_, v___x_1601_, v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1609_);
goto v___jp_1589_;
}
v___jp_1585_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_apply_1(v_flush_1583_, lean_box(0));
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
return v_a_1587_;
}
else
{
lean_object* v___x_1588_; 
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_box(0);
return v___x_1588_;
}
}
v___jp_1589_:
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_nat_dec_lt(v___x_1581_, v___x_1580_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v_failures_1578_);
lean_dec_ref(v_out_1573_);
goto v___jp_1585_;
}
else
{
lean_object* v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = lean_box(0);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = lean_usize_of_nat(v___x_1580_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1573_, v_failures_1578_, v___x_1592_, v___x_1593_, v___x_1591_);
lean_dec_ref(v_failures_1578_);
goto v___jp_1585_;
}
}
}
else
{
uint8_t v___x_1611_; 
lean_dec_ref(v_failures_1578_);
v___x_1611_ = l_Lake_BuildConfig_showProgress(v_cfg_1572_);
if (v___x_1611_ == 0)
{
lean_dec(v_numJobs_1579_);
lean_dec_ref(v_out_1573_);
goto v___jp_1576_;
}
else
{
uint8_t v_noBuild_1612_; uint8_t v_showSuccess_1613_; lean_object* v___y_1615_; 
v_noBuild_1612_ = lean_ctor_get_uint8(v_cfg_1572_, sizeof(void*)*5 + 2);
v_showSuccess_1613_ = lean_ctor_get_uint8(v_cfg_1572_, sizeof(void*)*5 + 5);
if (v_showSuccess_1613_ == 0)
{
lean_dec(v_numJobs_1579_);
lean_dec_ref(v_out_1573_);
goto v___jp_1576_;
}
else
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_nat_dec_eq(v_numJobs_1579_, v___x_1581_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_dec_eq(v_numJobs_1579_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = l_Nat_reprFast(v_numJobs_1579_);
v___x_1690_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__7));
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
v___y_1615_ = v___x_1691_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1692_; 
lean_dec(v_numJobs_1579_);
v___x_1692_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__8));
v___y_1615_ = v___x_1692_;
goto v___jp_1614_;
}
}
else
{
lean_object* v_putStr_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_numJobs_1579_);
v_putStr_1693_ = lean_ctor_get(v_out_1573_, 4);
lean_inc_ref(v_putStr_1693_);
lean_dec_ref(v_out_1573_);
v___x_1694_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1695_ = lean_apply_2(v_putStr_1693_, v___x_1694_, lean_box(0));
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
return v_a_1696_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1697_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1698_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1699_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1700_ = lean_unsigned_to_nat(82u);
v___x_1701_ = lean_unsigned_to_nat(4u);
v___x_1702_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1703_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1704_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1703_, v___x_1686_);
v___x_1705_ = lean_string_append(v___x_1702_, v___x_1704_);
lean_dec_ref(v___x_1704_);
v___x_1706_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1707_ = lean_string_append(v___x_1705_, v___x_1706_);
v___x_1708_ = lean_io_error_to_string(v_a_1697_);
v___x_1709_ = lean_string_append(v___x_1707_, v___x_1708_);
lean_dec_ref(v___x_1708_);
v___x_1710_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1711_ = lean_string_append(v___x_1709_, v___x_1710_);
v___x_1712_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1713_ = lean_string_append(v___x_1711_, v___x_1712_);
v___x_1714_ = l_mkPanicMessageWithDecl(v___x_1698_, v___x_1699_, v___x_1700_, v___x_1701_, v___x_1713_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1714_);
return v___x_1715_;
}
}
}
v___jp_1614_:
{
if (v_noBuild_1612_ == 0)
{
lean_object* v_putStr_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_putStr_1616_ = lean_ctor_get(v_out_1573_, 4);
lean_inc_ref(v_putStr_1616_);
lean_dec_ref(v_out_1573_);
v___x_1617_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___x_1618_ = lean_string_append(v___x_1617_, v___y_1615_);
lean_dec_ref(v___y_1615_);
v___x_1619_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1620_ = lean_string_append(v___x_1618_, v___x_1619_);
lean_inc_ref(v___x_1620_);
v___x_1621_ = lean_apply_2(v_putStr_1616_, v___x_1620_, lean_box(0));
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
lean_dec_ref(v___x_1620_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
return v_a_1622_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1650_; 
v_a_1623_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1650_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1650_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1627_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1628_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1629_ = lean_unsigned_to_nat(82u);
v___x_1630_ = lean_unsigned_to_nat(4u);
v___x_1631_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1632_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1633_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1632_, v_showSuccess_1613_);
v___x_1634_ = lean_string_append(v___x_1631_, v___x_1633_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1636_ = lean_string_append(v___x_1634_, v___x_1635_);
v___x_1637_ = lean_io_error_to_string(v_a_1623_);
v___x_1638_ = lean_string_append(v___x_1636_, v___x_1637_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
v___x_1641_ = l_String_quote(v___x_1620_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 3);
lean_ctor_set(v___x_1625_, 0, v___x_1641_);
v___x_1643_ = v___x_1625_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1644_ = l_Std_Format_defWidth;
v___x_1645_ = l_Std_Format_pretty(v___x_1643_, v___x_1644_, v___x_1581_, v___x_1581_);
v___x_1646_ = lean_string_append(v___x_1640_, v___x_1645_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_mkPanicMessageWithDecl(v___x_1627_, v___x_1628_, v___x_1629_, v___x_1630_, v___x_1646_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1647_);
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_putStr_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_putStr_1651_ = lean_ctor_get(v_out_1573_, 4);
lean_inc_ref(v_putStr_1651_);
lean_dec_ref(v_out_1573_);
v___x_1652_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__6));
v___x_1653_ = lean_string_append(v___x_1652_, v___y_1615_);
lean_dec_ref(v___y_1615_);
v___x_1654_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1655_ = lean_string_append(v___x_1653_, v___x_1654_);
lean_inc_ref(v___x_1655_);
v___x_1656_ = lean_apply_2(v_putStr_1651_, v___x_1655_, lean_box(0));
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
lean_dec_ref(v___x_1655_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
return v_a_1657_;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1685_; 
v_a_1658_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1660_ = v___x_1656_;
v_isShared_1661_ = v_isSharedCheck_1685_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1656_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1685_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1662_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1663_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1664_ = lean_unsigned_to_nat(82u);
v___x_1665_ = lean_unsigned_to_nat(4u);
v___x_1666_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1667_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1667_, v_noBuild_1612_);
v___x_1669_ = lean_string_append(v___x_1666_, v___x_1668_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
v___x_1672_ = lean_io_error_to_string(v_a_1658_);
v___x_1673_ = lean_string_append(v___x_1671_, v___x_1672_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1675_ = lean_string_append(v___x_1673_, v___x_1674_);
v___x_1676_ = l_String_quote(v___x_1655_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 3);
lean_ctor_set(v___x_1660_, 0, v___x_1676_);
v___x_1678_ = v___x_1660_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1679_ = l_Std_Format_defWidth;
v___x_1680_ = l_Std_Format_pretty(v___x_1678_, v___x_1679_, v___x_1581_, v___x_1581_);
v___x_1681_ = lean_string_append(v___x_1675_, v___x_1680_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = l_mkPanicMessageWithDecl(v___x_1662_, v___x_1663_, v___x_1664_, v___x_1665_, v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1682_);
return v___x_1683_;
}
}
}
}
}
}
}
v___jp_1576_:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_box(0);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1716_, lean_object* v_out_1717_, lean_object* v_result_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1716_, v_out_1717_, v_result_1718_);
lean_dec_ref(v_cfg_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(lean_object* v_self_1721_){
_start:
{
lean_object* v_toMonitorResult_1722_; 
v_toMonitorResult_1722_ = lean_ctor_get(v_self_1721_, 0);
lean_inc_ref(v_toMonitorResult_1722_);
return v_toMonitorResult_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0___boxed(lean_object* v_self_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(v_self_1723_);
lean_dec_ref(v_self_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg(){
_start:
{
lean_object* v___f_1727_; 
v___f_1727_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___boxed(lean_object* v___dummy_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg();
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1730_){
_start:
{
lean_object* v___f_1731_; 
v___f_1731_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1731_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1732_){
_start:
{
lean_object* v_out_1733_; 
v_out_1733_ = lean_ctor_get(v_self_1732_, 1);
if (lean_obj_tag(v_out_1733_) == 0)
{
uint8_t v___x_1734_; 
v___x_1734_ = 0;
return v___x_1734_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = 1;
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1736_);
lean_dec_ref(v_self_1736_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1739_, lean_object* v_self_1740_){
_start:
{
lean_object* v_out_1741_; 
v_out_1741_ = lean_ctor_get(v_self_1740_, 1);
if (lean_obj_tag(v_out_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = 0;
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = 1;
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_self_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1744_, v_self_1745_);
lean_dec_ref(v_self_1745_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1756_, lean_object* v_job_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_failures_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
lean_inc_ref(v_job_1757_);
v___x_1759_ = l_Lake_Job_toOpaque___redArg(v_job_1757_);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1760_);
v___x_1762_ = lean_array_push(v___x_1761_, v___x_1759_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1765_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1766_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1756_, v___x_1762_, v___x_1764_, v___x_1765_);
v_failures_1767_ = lean_ctor_get(v___x_1766_, 0);
v___x_1768_ = lean_array_get_size(v_failures_1767_);
v___x_1769_ = lean_nat_dec_eq(v___x_1768_, v___x_1763_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v_job_1757_);
v___x_1770_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1766_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v_task_1772_; lean_object* v___x_1773_; 
v_task_1772_ = lean_ctor_get(v_job_1757_, 0);
lean_inc_ref(v_task_1772_);
lean_dec_ref(v_job_1757_);
v___x_1773_ = lean_io_wait(v_task_1772_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1782_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v___x_1773_, 1);
lean_dec(v_unused_1783_);
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1782_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_a_1774_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v___x_1778_);
lean_ctor_set(v___x_1776_, 0, v___x_1766_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1766_);
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
else
{
lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1791_; 
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; lean_object* v_unused_1793_; 
v_unused_1792_ = lean_ctor_get(v___x_1773_, 1);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v___x_1773_, 0);
lean_dec(v_unused_1793_);
v___x_1785_ = v___x_1773_;
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
else
{
lean_dec(v___x_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1791_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 0);
lean_ctor_set(v___x_1785_, 1, v___x_1787_);
lean_ctor_set(v___x_1785_, 0, v___x_1766_);
v___x_1789_ = v___x_1785_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1794_, lean_object* v_job_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1794_, v_job_1795_);
lean_dec_ref(v_ctx_1794_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1798_, lean_object* v_ctx_1799_, lean_object* v_job_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1799_, v_job_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_ctx_1804_, lean_object* v_job_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1803_, v_ctx_1804_, v_job_1805_);
lean_dec_ref(v_ctx_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object* v_info_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lake_computeTextFileHash(v_info_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1814_ = lean_io_metadata(v_info_1810_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1826_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1826_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1826_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_modified_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint64_t v___x_1822_; lean_object* v___x_1824_; 
v_modified_1819_ = lean_ctor_get(v_a_1815_, 1);
lean_inc_ref(v_modified_1819_);
lean_dec(v_a_1815_);
v___x_1820_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1821_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1821_, 0, v_info_1810_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
lean_ctor_set(v___x_1821_, 2, v_modified_1819_);
v___x_1822_ = lean_unbox_uint64(v_a_1813_);
lean_dec(v_a_1813_);
lean_ctor_set_uint64(v___x_1821_, sizeof(void*)*3, v___x_1822_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1821_);
v___x_1824_ = v___x_1817_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1821_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_a_1813_);
lean_dec_ref(v_info_1810_);
v_a_1827_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1814_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1814_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v_info_1810_);
v_a_1835_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1812_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1812_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object* v_info_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object* v___x_1849_, lean_object* v_as_1850_, size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_b_1853_){
_start:
{
lean_object* v_a_1856_; uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_lt(v_i_1852_, v_sz_1851_);
if (v___x_1860_ == 0)
{
lean_dec_ref(v___x_1849_);
return v_b_1853_;
}
else
{
lean_object* v_snd_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1884_; 
v_snd_1861_ = lean_ctor_get(v_b_1853_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_b_1853_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v_b_1853_, 0);
lean_dec(v_unused_1885_);
v___x_1863_ = v_b_1853_;
v_isShared_1864_ = v_isSharedCheck_1884_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_snd_1861_);
lean_dec(v_b_1853_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1884_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1865_ = lean_box(0);
v_a_1866_ = lean_array_uget_borrowed(v_as_1850_, v_i_1852_);
v___x_1867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0));
lean_inc_ref(v___x_1849_);
v___x_1868_ = l_Lake_joinRelative(v___x_1849_, v___x_1867_);
lean_inc(v_a_1866_);
v___x_1869_ = l_Lake_joinRelative(v___x_1868_, v_a_1866_);
v___x_1870_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l_Lake_BuildTrace_mix(v_snd_1861_, v_a_1871_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1872_);
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1874_ = v___x_1863_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
v_a_1856_ = v___x_1874_;
goto v___jp_1855_;
}
}
else
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1870_, 1);
if (lean_obj_tag(v_a_1876_) == 11)
{
lean_object* v___x_1878_; 
lean_dec_ref_known(v_a_1876_, 2);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1878_ = v___x_1863_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_snd_1861_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
v_a_1856_ = v___x_1878_;
goto v___jp_1855_;
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec(v_a_1876_);
lean_dec_ref(v___x_1849_);
v___x_1880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1));
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1880_);
v___x_1882_ = v___x_1863_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_snd_1861_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
v___jp_1855_:
{
size_t v___x_1857_; size_t v___x_1858_; 
v___x_1857_ = ((size_t)1ULL);
v___x_1858_ = lean_usize_add(v_i_1852_, v___x_1857_);
v_i_1852_ = v___x_1858_;
v_b_1853_ = v_a_1856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object* v___x_1886_, lean_object* v_as_1887_, lean_object* v_sz_1888_, lean_object* v_i_1889_, lean_object* v_b_1890_, lean_object* v___y_1891_){
_start:
{
size_t v_sz_boxed_1892_; size_t v_i_boxed_1893_; lean_object* v_res_1894_; 
v_sz_boxed_1892_ = lean_unbox_usize(v_sz_1888_);
lean_dec(v_sz_1888_);
v_i_boxed_1893_ = lean_unbox_usize(v_i_1889_);
lean_dec(v_i_1889_);
v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1886_, v_as_1887_, v_sz_boxed_1892_, v_i_boxed_1893_, v_b_1890_);
lean_dec_ref(v_as_1887_);
return v_res_1894_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1));
v___x_1898_ = l_Lake_BuildTrace_nil(v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2);
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1913_);
return v___x_1915_;
}
}
static size_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1916_; size_t v_sz_1917_; 
v___x_1916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v_sz_1917_ = lean_array_size(v___x_1916_);
return v_sz_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t v_sz_1918_, size_t v_i_1919_, lean_object* v_bs_1920_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_lt(v_i_1919_, v_sz_1918_);
if (v___x_1922_ == 0)
{
return v_bs_1920_;
}
else
{
lean_object* v_v_1923_; lean_object* v_config_1924_; lean_object* v_dir_1925_; uint8_t v_bootstrap_1926_; lean_object* v_buildDir_1927_; lean_object* v___x_1928_; lean_object* v_bs_x27_1929_; lean_object* v_val_1931_; 
v_v_1923_ = lean_array_uget_borrowed(v_bs_1920_, v_i_1919_);
v_config_1924_ = lean_ctor_get(v_v_1923_, 6);
v_dir_1925_ = lean_ctor_get(v_v_1923_, 4);
lean_inc_ref(v_dir_1925_);
v_bootstrap_1926_ = lean_ctor_get_uint8(v_config_1924_, sizeof(void*)*28);
v_buildDir_1927_ = lean_ctor_get(v_config_1924_, 5);
lean_inc_ref(v_buildDir_1927_);
v___x_1928_ = lean_unsigned_to_nat(0u);
v_bs_x27_1929_ = lean_array_uset(v_bs_1920_, v_i_1919_, v___x_1928_);
if (v_bootstrap_1926_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v_buildDir_1927_);
lean_dec_ref(v_dir_1925_);
v___x_1936_ = lean_box(0);
v_val_1931_ = v___x_1936_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; size_t v_sz_1943_; size_t v___x_1944_; lean_object* v___x_1945_; lean_object* v_fst_1946_; 
v___x_1937_ = l_System_FilePath_normalize(v_buildDir_1927_);
v___x_1938_ = l_Lake_joinRelative(v_dir_1925_, v___x_1937_);
v___x_1939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0));
v___x_1940_ = l_Lake_joinRelative(v___x_1938_, v___x_1939_);
v___x_1941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v___x_1942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8);
v_sz_1943_ = lean_usize_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9);
v___x_1944_ = ((size_t)0ULL);
lean_inc_ref(v___x_1940_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1940_, v___x_1941_, v_sz_1943_, v___x_1944_, v___x_1942_);
v_fst_1946_ = lean_ctor_get(v___x_1945_, 0);
if (lean_obj_tag(v_fst_1946_) == 0)
{
lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
v_snd_1947_ = lean_ctor_get(v___x_1945_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v___x_1945_, 0);
lean_dec(v_unused_1956_);
v___x_1949_ = v___x_1945_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_dec(v___x_1945_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1940_);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_snd_1947_);
v___x_1952_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
v_val_1931_ = v___x_1953_;
goto v___jp_1930_;
}
}
}
else
{
lean_object* v_val_1957_; 
lean_inc_ref(v_fst_1946_);
lean_dec_ref(v___x_1945_);
lean_dec_ref(v___x_1940_);
v_val_1957_ = lean_ctor_get(v_fst_1946_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v_fst_1946_, 1);
v_val_1931_ = v_val_1957_;
goto v___jp_1930_;
}
}
v___jp_1930_:
{
size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_add(v_i_1919_, v___x_1932_);
v___x_1934_ = lean_array_uset(v_bs_x27_1929_, v_i_1919_, v_val_1931_);
v_i_1919_ = v___x_1933_;
v_bs_1920_ = v___x_1934_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object* v_sz_1958_, lean_object* v_i_1959_, lean_object* v_bs_1960_, lean_object* v___y_1961_){
_start:
{
size_t v_sz_boxed_1962_; size_t v_i_boxed_1963_; lean_object* v_res_1964_; 
v_sz_boxed_1962_ = lean_unbox_usize(v_sz_1958_);
lean_dec(v_sz_1958_);
v_i_boxed_1963_ = lean_unbox_usize(v_i_1959_);
lean_dec(v_i_1959_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_boxed_1962_, v_i_boxed_1963_, v_bs_1960_);
return v_res_1964_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = l_Lean_versionStringCore;
v___x_1967_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0));
v___x_1968_ = lean_string_append(v___x_1967_, v___x_1966_);
return v___x_1968_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2));
v___x_1971_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1);
v___x_1972_ = lean_string_append(v___x_1971_, v___x_1970_);
return v___x_1972_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_nat_to_int(v___x_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5(void){
_start:
{
uint32_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = 0;
v___x_1976_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4);
v___x_1977_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set_uint32(v___x_1977_, sizeof(void*)*1, v___x_1975_);
return v___x_1977_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_unsigned_to_nat(16u);
v___x_1980_ = lean_mk_array(v___x_1979_, v___x_1978_);
return v___x_1980_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6);
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1981_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object* v_ws_1986_, lean_object* v_cfg_1987_, lean_object* v_jobs_1988_, lean_object* v_cancelTk_x3f_1989_){
_start:
{
uint8_t v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; uint8_t v___y_1996_; uint8_t v___y_1997_; uint8_t v___y_1998_; lean_object* v___y_1999_; uint8_t v___y_2000_; uint8_t v___y_2001_; lean_object* v___y_2002_; lean_object* v_val_2003_; uint8_t v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; uint8_t v___y_2026_; uint8_t v___y_2027_; lean_object* v___y_2028_; uint8_t v___y_2029_; uint8_t v___y_2030_; lean_object* v___y_2031_; lean_object* v_val_2034_; uint8_t v___x_2060_; 
v___x_2060_ = l_System_Platform_isOSX;
if (v___x_2060_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_2061_; 
v_macosxDeploymentTarget_x3f_2061_ = lean_ctor_get(v_cfg_1987_, 4);
lean_inc(v_macosxDeploymentTarget_x3f_2061_);
v_val_2034_ = v_macosxDeploymentTarget_x3f_2061_;
goto v___jp_2033_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_2062_; 
v_macosxDeploymentTarget_x3f_2062_ = lean_ctor_get(v_cfg_1987_, 4);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_2062_) == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___y_2066_; 
v___x_2063_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8));
v___x_2064_ = lean_io_getenv(v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9));
v___y_2066_ = v___x_2068_;
goto v___jp_2065_;
}
else
{
lean_object* v_val_2069_; 
v_val_2069_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v___x_2064_, 1);
v___y_2066_ = v_val_2069_;
goto v___jp_2065_;
}
v___jp_2065_:
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___y_2066_);
v_val_2034_ = v___x_2067_;
goto v___jp_2033_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_2062_);
v_val_2034_ = v_macosxDeploymentTarget_x3f_2062_;
goto v___jp_2033_;
}
}
v___jp_1991_:
{
lean_object* v_lakeEnv_2004_; lean_object* v_packages_2005_; size_t v_sz_2006_; size_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint64_t v___x_2011_; uint64_t v___x_2012_; uint64_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_lakeEnv_2004_ = lean_ctor_get(v_ws_1986_, 0);
v_packages_2005_ = lean_ctor_get(v_ws_1986_, 4);
v_sz_2006_ = lean_array_size(v_packages_2005_);
v___x_2007_ = ((size_t)0ULL);
lean_inc_ref(v_packages_2005_);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_2006_, v___x_2007_, v_packages_2005_);
v___x_2009_ = lean_alloc_ctor(0, 5, 6);
lean_ctor_set(v___x_2009_, 0, v___y_1995_);
lean_ctor_set(v___x_2009_, 1, v___y_1999_);
lean_ctor_set(v___x_2009_, 2, v___y_1994_);
lean_ctor_set(v___x_2009_, 3, v___y_2002_);
lean_ctor_set(v___x_2009_, 4, v___y_1993_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*5, v___y_1997_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*5 + 1, v___y_2001_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*5 + 2, v___y_1996_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*5 + 3, v___y_1998_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*5 + 4, v___y_2000_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*5 + 5, v___y_1992_);
v___x_2010_ = l_Lake_Env_leanGithash(v_lakeEnv_2004_);
v___x_2011_ = l_Lake_Hash_nil;
v___x_2012_ = lean_string_hash(v___x_2010_);
v___x_2013_ = lean_uint64_mix_hash(v___x_2011_, v___x_2012_);
v___x_2014_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3);
v___x_2015_ = lean_string_append(v___x_2014_, v___x_2010_);
lean_dec_ref(v___x_2010_);
v___x_2016_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_2017_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5);
v___x_2018_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2018_, 0, v___x_2015_);
lean_ctor_set(v___x_2018_, 1, v___x_2016_);
lean_ctor_set(v___x_2018_, 2, v___x_2017_);
lean_ctor_set_uint64(v___x_2018_, sizeof(void*)*3, v___x_2013_);
v___x_2019_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2009_);
lean_ctor_set(v___x_2019_, 1, v_ws_1986_);
lean_ctor_set(v___x_2019_, 2, v___x_2018_);
lean_ctor_set(v___x_2019_, 3, v___x_2008_);
lean_ctor_set(v___x_2019_, 4, v_jobs_1988_);
lean_ctor_set(v___x_2019_, 5, v_val_2003_);
lean_ctor_set(v___x_2019_, 6, v_cancelTk_x3f_1989_);
return v___x_2019_;
}
v___jp_2020_:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_box(0);
v___y_1992_ = v___y_2021_;
v___y_1993_ = v___y_2024_;
v___y_1994_ = v___y_2023_;
v___y_1995_ = v___y_2022_;
v___y_1996_ = v___y_2026_;
v___y_1997_ = v___y_2025_;
v___y_1998_ = v___y_2027_;
v___y_1999_ = v___y_2028_;
v___y_2000_ = v___y_2030_;
v___y_2001_ = v___y_2029_;
v___y_2002_ = v___y_2031_;
v_val_2003_ = v___x_2032_;
goto v___jp_1991_;
}
v___jp_2033_:
{
lean_object* v_outputsFile_x3f_2035_; 
v_outputsFile_x3f_2035_ = lean_ctor_get(v_cfg_1987_, 1);
lean_inc(v_outputsFile_x3f_2035_);
if (lean_obj_tag(v_outputsFile_x3f_2035_) == 0)
{
lean_object* v_toLogConfig_2036_; uint8_t v_oldMode_2037_; uint8_t v_trustHash_2038_; uint8_t v_noBuild_2039_; uint8_t v_failFast_2040_; uint8_t v_verbosity_2041_; uint8_t v_showSuccess_2042_; lean_object* v_outputsIdx_2043_; lean_object* v_leanOptOverrides_2044_; 
v_toLogConfig_2036_ = lean_ctor_get(v_cfg_1987_, 0);
lean_inc_ref(v_toLogConfig_2036_);
v_oldMode_2037_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5);
v_trustHash_2038_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 1);
v_noBuild_2039_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 2);
v_failFast_2040_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 3);
v_verbosity_2041_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 4);
v_showSuccess_2042_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 5);
v_outputsIdx_2043_ = lean_ctor_get(v_cfg_1987_, 2);
lean_inc(v_outputsIdx_2043_);
v_leanOptOverrides_2044_ = lean_ctor_get(v_cfg_1987_, 3);
lean_inc(v_leanOptOverrides_2044_);
lean_dec_ref(v_cfg_1987_);
v___y_2021_ = v_showSuccess_2042_;
v___y_2022_ = v_toLogConfig_2036_;
v___y_2023_ = v_outputsIdx_2043_;
v___y_2024_ = v_val_2034_;
v___y_2025_ = v_oldMode_2037_;
v___y_2026_ = v_noBuild_2039_;
v___y_2027_ = v_failFast_2040_;
v___y_2028_ = v_outputsFile_x3f_2035_;
v___y_2029_ = v_trustHash_2038_;
v___y_2030_ = v_verbosity_2041_;
v___y_2031_ = v_leanOptOverrides_2044_;
goto v___jp_2020_;
}
else
{
lean_object* v_toLogConfig_2045_; uint8_t v_oldMode_2046_; uint8_t v_trustHash_2047_; uint8_t v_noBuild_2048_; uint8_t v_failFast_2049_; uint8_t v_verbosity_2050_; uint8_t v_showSuccess_2051_; lean_object* v_outputsIdx_2052_; lean_object* v_leanOptOverrides_2053_; lean_object* v_packages_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_toLogConfig_2045_ = lean_ctor_get(v_cfg_1987_, 0);
lean_inc_ref(v_toLogConfig_2045_);
v_oldMode_2046_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5);
v_trustHash_2047_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 1);
v_noBuild_2048_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 2);
v_failFast_2049_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 3);
v_verbosity_2050_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 4);
v_showSuccess_2051_ = lean_ctor_get_uint8(v_cfg_1987_, sizeof(void*)*5 + 5);
v_outputsIdx_2052_ = lean_ctor_get(v_cfg_1987_, 2);
lean_inc(v_outputsIdx_2052_);
v_leanOptOverrides_2053_ = lean_ctor_get(v_cfg_1987_, 3);
lean_inc(v_leanOptOverrides_2053_);
lean_dec_ref(v_cfg_1987_);
v_packages_2054_ = lean_ctor_get(v_ws_1986_, 4);
v___x_2055_ = lean_array_get_size(v_packages_2054_);
v___x_2056_ = lean_nat_dec_lt(v_outputsIdx_2052_, v___x_2055_);
if (v___x_2056_ == 0)
{
v___y_2021_ = v_showSuccess_2051_;
v___y_2022_ = v_toLogConfig_2045_;
v___y_2023_ = v_outputsIdx_2052_;
v___y_2024_ = v_val_2034_;
v___y_2025_ = v_oldMode_2046_;
v___y_2026_ = v_noBuild_2048_;
v___y_2027_ = v_failFast_2049_;
v___y_2028_ = v_outputsFile_x3f_2035_;
v___y_2029_ = v_trustHash_2047_;
v___y_2030_ = v_verbosity_2050_;
v___y_2031_ = v_leanOptOverrides_2053_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7);
v___x_2058_ = lean_st_mk_ref(v___x_2057_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
v___y_1992_ = v_showSuccess_2051_;
v___y_1993_ = v_val_2034_;
v___y_1994_ = v_outputsIdx_2052_;
v___y_1995_ = v_toLogConfig_2045_;
v___y_1996_ = v_noBuild_2048_;
v___y_1997_ = v_oldMode_2046_;
v___y_1998_ = v_failFast_2049_;
v___y_1999_ = v_outputsFile_x3f_2035_;
v___y_2000_ = v_verbosity_2050_;
v___y_2001_ = v_trustHash_2047_;
v___y_2002_ = v_leanOptOverrides_2053_;
v_val_2003_ = v___x_2059_;
goto v___jp_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object* v_ws_2070_, lean_object* v_cfg_2071_, lean_object* v_jobs_2072_, lean_object* v_cancelTk_x3f_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2070_, v_cfg_2071_, v_jobs_2072_, v_cancelTk_x3f_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_log_2084_; uint8_t v_action_2085_; uint8_t v_wantsRebuild_2086_; uint8_t v_canceled_2087_; lean_object* v_trace_2088_; lean_object* v_buildTime_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2118_; 
v_log_2084_ = lean_ctor_get(v___y_2082_, 0);
v_action_2085_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*3);
v_wantsRebuild_2086_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*3 + 1);
v_canceled_2087_ = lean_ctor_get_uint8(v___y_2082_, sizeof(void*)*3 + 2);
v_trace_2088_ = lean_ctor_get(v___y_2082_, 1);
v_buildTime_2089_ = lean_ctor_get(v___y_2082_, 2);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___y_2082_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2091_ = v___y_2082_;
v_isShared_2092_ = v_isSharedCheck_2118_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_buildTime_2089_);
lean_inc(v_trace_2088_);
lean_inc(v_log_2084_);
lean_dec(v___y_2082_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2118_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_apply_7(v_build_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v_log_2084_, lean_box(0));
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2105_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_a_2095_ = lean_ctor_get(v___x_2093_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2097_ = v___x_2093_;
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v_a_2095_);
v___x_2100_ = v___x_2091_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2095_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_trace_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_buildTime_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*3, v_action_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*3 + 1, v_wantsRebuild_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*3 + 2, v_canceled_2087_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2100_);
v___x_2102_ = v___x_2097_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2094_);
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
else
{
lean_object* v_a_2106_; lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_a_2106_ = lean_ctor_get(v___x_2093_, 0);
v_a_2107_ = lean_ctor_get(v___x_2093_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2109_ = v___x_2093_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_inc(v_a_2106_);
lean_dec(v___x_2093_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v_a_2107_);
v___x_2112_ = v___x_2091_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2107_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_trace_2088_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_buildTime_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2116_, sizeof(void*)*3, v_action_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2116_, sizeof(void*)*3 + 1, v_wantsRebuild_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2116_, sizeof(void*)*3 + 2, v_canceled_2087_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2112_);
v___x_2114_ = v___x_2109_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2106_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_2129_, lean_object* v_build_2130_, lean_object* v_caption_2131_){
_start:
{
lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___f_2133_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2133_, 0, v_build_2130_);
v___x_2134_ = lean_box(0);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_box(1);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_st_mk_ref(v___x_2137_);
v___x_2140_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_2141_ = l_Lake_Job_async___redArg(v___x_2134_, v___f_2133_, v___x_2135_, v_caption_2131_, v___x_2140_, v___x_2138_, v___x_2136_, v___x_2139_, v_bctx_2129_);
v___x_2142_ = lean_st_ref_get(v___x_2139_);
lean_dec(v___x_2139_);
lean_dec(v___x_2142_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_2143_, lean_object* v_build_2144_, lean_object* v_caption_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2143_, v_build_2144_, v_caption_2145_);
lean_dec_ref(v_bctx_2143_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_2148_, lean_object* v_bctx_2149_, lean_object* v_build_2150_, lean_object* v_caption_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2149_, v_build_2150_, v_caption_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_bctx_2155_, lean_object* v_build_2156_, lean_object* v_caption_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_2154_, v_bctx_2155_, v_build_2156_, v_caption_2157_);
lean_dec_ref(v_bctx_2155_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_2160_, uint8_t v___x_2161_, uint8_t v___x_2162_, lean_object* v_as_2163_, size_t v_i_2164_, size_t v_stop_2165_, lean_object* v_b_2166_){
_start:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_usize_dec_eq(v_i_2164_, v_stop_2165_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; 
v___x_2169_ = lean_array_uget_borrowed(v_as_2163_, v_i_2164_);
lean_inc_ref(v___x_2160_);
v___x_2170_ = l_Lake_logToStream(v___x_2169_, v___x_2160_, v___x_2161_, v___x_2162_);
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2164_, v___x_2171_);
v_i_2164_ = v___x_2172_;
v_b_2166_ = v___x_2170_;
goto _start;
}
else
{
lean_dec_ref(v___x_2160_);
return v_b_2166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v_as_2177_, lean_object* v_i_2178_, lean_object* v_stop_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v___x_1088__boxed_2182_; uint8_t v___x_1089__boxed_2183_; size_t v_i_boxed_2184_; size_t v_stop_boxed_2185_; lean_object* v_res_2186_; 
v___x_1088__boxed_2182_ = lean_unbox(v___x_2175_);
v___x_1089__boxed_2183_ = lean_unbox(v___x_2176_);
v_i_boxed_2184_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_stop_boxed_2185_ = lean_unbox_usize(v_stop_2179_);
lean_dec(v_stop_2179_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2174_, v___x_1088__boxed_2182_, v___x_1089__boxed_2183_, v_as_2177_, v_i_boxed_2184_, v_stop_boxed_2185_, v_b_2180_);
lean_dec_ref(v_as_2177_);
return v_res_2186_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
if (lean_obj_tag(v_x_2190_) == 0)
{
uint8_t v___x_2191_; 
v___x_2191_ = 1;
return v___x_2191_;
}
else
{
uint8_t v___x_2192_; 
v___x_2192_ = 0;
return v___x_2192_;
}
}
else
{
if (lean_obj_tag(v_x_2190_) == 0)
{
uint8_t v___x_2193_; 
v___x_2193_ = 0;
return v___x_2193_;
}
else
{
lean_object* v_val_2194_; uint8_t v___x_2195_; 
v_val_2194_ = lean_ctor_get(v_x_2190_, 0);
v___x_2195_ = lean_unbox(v_val_2194_);
if (v___x_2195_ == 0)
{
lean_object* v_val_2196_; uint8_t v___x_2197_; 
v_val_2196_ = lean_ctor_get(v_x_2189_, 0);
v___x_2197_ = lean_unbox(v_val_2196_);
if (v___x_2197_ == 0)
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_lt(v___x_2187_, v___x_2188_);
return v___x_2198_;
}
else
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_unbox(v_val_2194_);
return v___x_2199_;
}
}
else
{
lean_object* v_val_2200_; uint8_t v___x_2201_; 
v_val_2200_ = lean_ctor_get(v_x_2189_, 0);
v___x_2201_ = lean_unbox(v_val_2200_);
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v___x_2202_, lean_object* v___x_2203_, lean_object* v_x_2204_, lean_object* v_x_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_2202_, v___x_2203_, v_x_2204_, v_x_2205_);
lean_dec(v_x_2205_);
lean_dec(v_x_2204_);
lean_dec(v___x_2203_);
lean_dec(v___x_2202_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_2208_, uint8_t v___x_2209_, uint8_t v___x_2210_, lean_object* v_bctx_2211_, lean_object* v_out_2212_, lean_object* v_outputsFile_2213_){
_start:
{
lean_object* v___y_2218_; lean_object* v___y_2219_; uint8_t v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v_outputsRef_x3f_2241_; 
v_outputsRef_x3f_2241_ = lean_ctor_get(v_bctx_2211_, 5);
lean_inc(v_outputsRef_x3f_2241_);
if (lean_obj_tag(v_outputsRef_x3f_2241_) == 1)
{
lean_object* v_toContext_2242_; lean_object* v_toBuildConfig_2243_; lean_object* v_val_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2360_; 
v_toContext_2242_ = lean_ctor_get(v_bctx_2211_, 1);
lean_inc(v_toContext_2242_);
v_toBuildConfig_2243_ = lean_ctor_get(v_bctx_2211_, 0);
lean_inc_ref(v_toBuildConfig_2243_);
lean_dec_ref(v_bctx_2211_);
v_val_2244_ = lean_ctor_get(v_outputsRef_x3f_2241_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_outputsRef_x3f_2241_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2246_ = v_outputsRef_x3f_2241_;
v_isShared_2247_ = v_isSharedCheck_2360_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_val_2244_);
lean_dec(v_outputsRef_x3f_2241_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2360_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v_lakeEnv_2248_; lean_object* v_packages_2249_; uint8_t v_verbosity_2250_; lean_object* v_outputsIdx_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_lakeEnv_2248_ = lean_ctor_get(v_toContext_2242_, 0);
lean_inc_ref(v_lakeEnv_2248_);
v_packages_2249_ = lean_ctor_get(v_toContext_2242_, 4);
lean_inc_ref(v_packages_2249_);
lean_dec(v_toContext_2242_);
v_verbosity_2250_ = lean_ctor_get_uint8(v_toBuildConfig_2243_, sizeof(void*)*5 + 4);
v_outputsIdx_2251_ = lean_ctor_get(v_toBuildConfig_2243_, 2);
lean_inc(v_outputsIdx_2251_);
lean_dec_ref(v_toBuildConfig_2243_);
v___x_2252_ = lean_array_get_size(v_packages_2249_);
v___x_2253_ = lean_nat_dec_lt(v_outputsIdx_2251_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v_putStr_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v_outputsIdx_2251_);
lean_dec_ref(v_packages_2249_);
lean_dec_ref(v_lakeEnv_2248_);
lean_del_object(v___x_2246_);
lean_dec(v_val_2244_);
lean_dec_ref(v_outputsFile_2213_);
lean_dec_ref(v___x_2208_);
v_putStr_2254_ = lean_ctor_get(v_out_2212_, 4);
lean_inc_ref(v_putStr_2254_);
lean_dec_ref(v_out_2212_);
v___x_2255_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_2256_ = lean_apply_2(v_putStr_2254_, v___x_2255_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_dec_ref_known(v___x_2256_, 1);
goto v___jp_2237_;
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2259_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2260_ = lean_unsigned_to_nat(82u);
v___x_2261_ = lean_unsigned_to_nat(4u);
v___x_2262_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2263_ = lean_io_error_to_string(v_a_2257_);
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_2268_ = lean_string_append(v___x_2266_, v___x_2267_);
v___x_2269_ = l_mkPanicMessageWithDecl(v___x_2258_, v___x_2259_, v___x_2260_, v___x_2261_, v___x_2268_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2269_);
goto v___jp_2237_;
}
}
else
{
lean_object* v___x_2271_; lean_object* v_config_2272_; lean_object* v_baseName_2273_; lean_object* v_toLeanConfig_2274_; lean_object* v_enableArtifactCache_x3f_2275_; uint8_t v___y_2277_; uint8_t v___y_2339_; uint8_t v___y_2347_; 
v___x_2271_ = lean_array_fget_borrowed(v_packages_2249_, v_outputsIdx_2251_);
v_config_2272_ = lean_ctor_get(v___x_2271_, 6);
v_baseName_2273_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_baseName_2273_);
v_toLeanConfig_2274_ = lean_ctor_get(v_config_2272_, 1);
lean_inc_ref(v_toLeanConfig_2274_);
v_enableArtifactCache_x3f_2275_ = lean_ctor_get(v_config_2272_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_2275_) == 0)
{
lean_object* v_enableArtifactCache_x3f_2348_; 
v_enableArtifactCache_x3f_2348_ = lean_ctor_get(v_lakeEnv_2248_, 6);
lean_inc(v_enableArtifactCache_x3f_2348_);
lean_dec_ref(v_lakeEnv_2248_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2348_) == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_config_2351_; lean_object* v_enableArtifactCache_x3f_2352_; 
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_array_fget(v_packages_2249_, v___x_2349_);
lean_dec_ref(v_packages_2249_);
v_config_2351_ = lean_ctor_get(v___x_2350_, 6);
lean_inc_ref(v_config_2351_);
lean_dec(v___x_2350_);
v_enableArtifactCache_x3f_2352_ = lean_ctor_get(v_config_2351_, 24);
lean_inc(v_enableArtifactCache_x3f_2352_);
lean_dec_ref(v_config_2351_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2352_) == 0)
{
uint8_t v___x_2353_; 
v___x_2353_ = 0;
v___y_2339_ = v___x_2353_;
goto v___jp_2338_;
}
else
{
lean_object* v_val_2354_; uint8_t v___x_2355_; 
v_val_2354_ = lean_ctor_get(v_enableArtifactCache_x3f_2352_, 0);
lean_inc(v_val_2354_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2352_, 1);
v___x_2355_ = lean_unbox(v_val_2354_);
lean_dec(v_val_2354_);
v___y_2347_ = v___x_2355_;
goto v___jp_2346_;
}
}
else
{
lean_object* v_val_2356_; uint8_t v___x_2357_; 
lean_dec_ref(v_packages_2249_);
v_val_2356_ = lean_ctor_get(v_enableArtifactCache_x3f_2348_, 0);
lean_inc(v_val_2356_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2348_, 1);
v___x_2357_ = lean_unbox(v_val_2356_);
lean_dec(v_val_2356_);
v___y_2347_ = v___x_2357_;
goto v___jp_2346_;
}
}
else
{
lean_object* v_val_2358_; uint8_t v___x_2359_; 
lean_inc_ref(v_enableArtifactCache_x3f_2275_);
lean_dec_ref(v_packages_2249_);
lean_dec_ref(v_lakeEnv_2248_);
v_val_2358_ = lean_ctor_get(v_enableArtifactCache_x3f_2275_, 0);
lean_inc(v_val_2358_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2275_, 1);
v___x_2359_ = lean_unbox(v_val_2358_);
lean_dec(v_val_2358_);
v___y_2347_ = v___x_2359_;
goto v___jp_2346_;
}
v___jp_2276_:
{
lean_object* v___x_2278_; lean_object* v_platformIndependent_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2278_ = lean_st_ref_get(v_val_2244_);
lean_dec(v_val_2244_);
v_platformIndependent_2279_ = lean_ctor_get(v_toLeanConfig_2274_, 10);
lean_inc(v_platformIndependent_2279_);
lean_dec_ref(v_toLeanConfig_2274_);
v___x_2280_ = lean_box(v___x_2253_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2280_);
v___x_2282_ = v___x_2246_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2283_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_outputsIdx_2251_, v___x_2252_, v_platformIndependent_2279_, v___x_2282_);
lean_dec_ref(v___x_2282_);
lean_dec(v_platformIndependent_2279_);
lean_dec(v_outputsIdx_2251_);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_2286_ = l_Lake_CacheMap_writeFile(v_outputsFile_2213_, v___x_2278_, v___x_2283_, v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 1);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 2);
v___x_2288_ = lean_array_get_size(v_a_2287_);
v___x_2289_ = lean_nat_dec_eq(v___x_2288_, v___x_2284_);
if (v___x_2289_ == 0)
{
if (v___y_2277_ == 0)
{
lean_dec(v_a_2287_);
lean_dec_ref(v_out_2212_);
lean_dec_ref(v___x_2208_);
goto v___jp_2215_;
}
else
{
lean_object* v_putStr_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_putStr_2290_ = lean_ctor_get(v_out_2212_, 4);
lean_inc_ref(v_putStr_2290_);
lean_dec_ref(v_out_2212_);
v___x_2291_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_2292_ = lean_apply_2(v_putStr_2290_, v___x_2291_, lean_box(0));
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_dec_ref_known(v___x_2292_, 1);
v___y_2218_ = v_a_2287_;
v___y_2219_ = v___x_2284_;
goto v___jp_2217_;
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2295_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2296_ = lean_unsigned_to_nat(82u);
v___x_2297_ = lean_unsigned_to_nat(4u);
v___x_2298_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2299_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2300_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2299_, v___y_2277_);
v___x_2301_ = lean_string_append(v___x_2298_, v___x_2300_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2303_ = lean_string_append(v___x_2301_, v___x_2302_);
v___x_2304_ = lean_io_error_to_string(v_a_2293_);
v___x_2305_ = lean_string_append(v___x_2303_, v___x_2304_);
lean_dec_ref(v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
v___x_2308_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
v___x_2310_ = l_mkPanicMessageWithDecl(v___x_2294_, v___x_2295_, v___x_2296_, v___x_2297_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2310_);
v___y_2218_ = v_a_2287_;
v___y_2219_ = v___x_2284_;
goto v___jp_2217_;
}
}
}
else
{
lean_dec(v_a_2287_);
lean_dec_ref(v_out_2212_);
lean_dec_ref(v___x_2208_);
goto v___jp_2215_;
}
}
else
{
lean_object* v_a_2312_; lean_object* v_putStr_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_a_2312_ = lean_ctor_get(v___x_2286_, 1);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2286_, 2);
v_putStr_2313_ = lean_ctor_get(v_out_2212_, 4);
lean_inc_ref(v_putStr_2313_);
lean_dec_ref(v_out_2212_);
v___x_2314_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_2315_ = lean_apply_2(v_putStr_2313_, v___x_2314_, lean_box(0));
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_dec_ref_known(v___x_2315_, 1);
v___y_2227_ = v___y_2277_;
v___y_2228_ = v___x_2284_;
v___y_2229_ = v_a_2312_;
goto v___jp_2226_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2318_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2319_ = lean_unsigned_to_nat(82u);
v___x_2320_ = lean_unsigned_to_nat(4u);
v___x_2321_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2322_, v___x_2253_);
v___x_2324_ = lean_string_append(v___x_2321_, v___x_2323_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2326_ = lean_string_append(v___x_2324_, v___x_2325_);
v___x_2327_ = lean_io_error_to_string(v_a_2316_);
v___x_2328_ = lean_string_append(v___x_2326_, v___x_2327_);
lean_dec_ref(v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v___x_2333_ = l_mkPanicMessageWithDecl(v___x_2317_, v___x_2318_, v___x_2319_, v___x_2320_, v___x_2332_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2333_);
v___y_2227_ = v___y_2277_;
v___y_2228_ = v___x_2284_;
v___y_2229_ = v_a_2312_;
goto v___jp_2226_;
}
}
}
}
v___jp_2336_:
{
if (v_verbosity_2250_ == 2)
{
v___y_2277_ = v___x_2253_;
goto v___jp_2276_;
}
else
{
uint8_t v___x_2337_; 
v___x_2337_ = 0;
v___y_2277_ = v___x_2337_;
goto v___jp_2276_;
}
}
v___jp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2340_ = l_Lean_Name_toString(v_baseName_2273_, v___y_2339_);
v___x_2341_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_2342_ = lean_string_append(v___x_2340_, v___x_2341_);
v___x_2343_ = 2;
v___x_2344_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*1, v___x_2343_);
lean_inc_ref(v___x_2208_);
v___x_2345_ = l_Lake_logToStream(v___x_2344_, v___x_2208_, v___x_2209_, v___x_2210_);
lean_dec_ref_known(v___x_2344_, 1);
goto v___jp_2336_;
}
v___jp_2346_:
{
if (v___y_2347_ == 0)
{
v___y_2339_ = v___y_2347_;
goto v___jp_2338_;
}
else
{
lean_dec(v_baseName_2273_);
goto v___jp_2336_;
}
}
}
}
}
else
{
lean_object* v_putStr_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec(v_outputsRef_x3f_2241_);
lean_dec_ref(v_outputsFile_2213_);
lean_dec_ref(v_bctx_2211_);
lean_dec_ref(v___x_2208_);
v_putStr_2361_ = lean_ctor_get(v_out_2212_, 4);
lean_inc_ref(v_putStr_2361_);
lean_dec_ref(v_out_2212_);
v___x_2362_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_2363_ = lean_apply_2(v_putStr_2361_, v___x_2362_, lean_box(0));
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref_known(v___x_2363_, 1);
goto v___jp_2239_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2366_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2367_ = lean_unsigned_to_nat(82u);
v___x_2368_ = lean_unsigned_to_nat(4u);
v___x_2369_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2370_ = lean_io_error_to_string(v_a_2364_);
v___x_2371_ = lean_string_append(v___x_2369_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2373_ = lean_string_append(v___x_2371_, v___x_2372_);
v___x_2374_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_2375_ = lean_string_append(v___x_2373_, v___x_2374_);
v___x_2376_ = l_mkPanicMessageWithDecl(v___x_2365_, v___x_2366_, v___x_2367_, v___x_2368_, v___x_2375_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2376_);
goto v___jp_2239_;
}
}
v___jp_2215_:
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_box(0);
return v___x_2216_;
}
v___jp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_array_get_size(v___y_2218_);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_nat_dec_lt(v___y_2219_, v___x_2220_);
if (v___x_2222_ == 0)
{
lean_dec_ref(v___y_2218_);
lean_dec_ref(v___x_2208_);
return v___x_2221_;
}
else
{
size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = lean_usize_of_nat(v___x_2220_);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2208_, v___x_2209_, v___x_2210_, v___y_2218_, v___x_2223_, v___x_2224_, v___x_2221_);
lean_dec_ref(v___y_2218_);
return v___x_2225_;
}
}
v___jp_2226_:
{
if (v___y_2227_ == 0)
{
lean_object* v___x_2230_; 
lean_dec_ref(v___y_2229_);
lean_dec_ref(v___x_2208_);
v___x_2230_ = lean_box(0);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2231_ = lean_array_get_size(v___y_2229_);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_nat_dec_lt(v___y_2228_, v___x_2231_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v___y_2229_);
lean_dec_ref(v___x_2208_);
return v___x_2232_;
}
else
{
size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_usize_of_nat(v___x_2231_);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2208_, v___x_2209_, v___x_2210_, v___y_2229_, v___x_2234_, v___x_2235_, v___x_2232_);
lean_dec_ref(v___y_2229_);
return v___x_2236_;
}
}
}
v___jp_2237_:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_box(0);
return v___x_2238_;
}
v___jp_2239_:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_box(0);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2378_, lean_object* v___x_2379_, lean_object* v___x_2380_, lean_object* v_bctx_2381_, lean_object* v_out_2382_, lean_object* v_outputsFile_2383_, lean_object* v_a_2384_){
_start:
{
uint8_t v___x_1332__boxed_2385_; uint8_t v___x_1333__boxed_2386_; lean_object* v_res_2387_; 
v___x_1332__boxed_2385_ = lean_unbox(v___x_2379_);
v___x_1333__boxed_2386_ = lean_unbox(v___x_2380_);
v_res_2387_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2378_, v___x_1332__boxed_2385_, v___x_1333__boxed_2386_, v_bctx_2381_, v_out_2382_, v_outputsFile_2383_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2388_, lean_object* v_bctx_2389_, lean_object* v_mctx_2390_, lean_object* v_result_2391_){
_start:
{
lean_object* v___y_2394_; lean_object* v_out_2397_; uint8_t v_outLv_2398_; uint8_t v_useAnsi_2399_; lean_object* v_toMonitorResult_2400_; lean_object* v_out_2401_; lean_object* v___x_2417_; lean_object* v_outputsFile_x3f_2418_; 
v_out_2397_ = lean_ctor_get(v_mctx_2390_, 1);
lean_inc_ref_n(v_out_2397_, 2);
v_outLv_2398_ = lean_ctor_get_uint8(v_mctx_2390_, sizeof(void*)*4);
v_useAnsi_2399_ = lean_ctor_get_uint8(v_mctx_2390_, sizeof(void*)*4 + 4);
lean_dec_ref(v_mctx_2390_);
v_toMonitorResult_2400_ = lean_ctor_get(v_result_2391_, 0);
lean_inc_ref_n(v_toMonitorResult_2400_, 2);
v_out_2401_ = lean_ctor_get(v_result_2391_, 1);
lean_inc_ref(v_out_2401_);
lean_dec_ref(v_result_2391_);
v___x_2417_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2388_, v_out_2397_, v_toMonitorResult_2400_);
v_outputsFile_x3f_2418_ = lean_ctor_get(v_cfg_2388_, 1);
if (lean_obj_tag(v_outputsFile_x3f_2418_) == 1)
{
lean_object* v_val_2419_; lean_object* v___x_2420_; 
v_val_2419_ = lean_ctor_get(v_outputsFile_x3f_2418_, 0);
lean_inc(v_val_2419_);
lean_inc_ref(v_out_2397_);
v___x_2420_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2397_, v_outLv_2398_, v_useAnsi_2399_, v_bctx_2389_, v_out_2397_, v_val_2419_);
goto v___jp_2402_;
}
else
{
lean_dec_ref(v_out_2397_);
lean_dec_ref(v_bctx_2389_);
goto v___jp_2402_;
}
v___jp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_mk_io_user_error(v___y_2394_);
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
v___jp_2402_:
{
if (lean_obj_tag(v_out_2401_) == 0)
{
uint8_t v_noBuild_2403_; 
v_noBuild_2403_ = lean_ctor_get_uint8(v_cfg_2388_, sizeof(void*)*5 + 2);
lean_dec_ref(v_cfg_2388_);
if (v_noBuild_2403_ == 0)
{
lean_object* v_a_2404_; 
lean_dec_ref(v_toMonitorResult_2400_);
v_a_2404_ = lean_ctor_get(v_out_2401_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v_out_2401_, 1);
v___y_2394_ = v_a_2404_;
goto v___jp_2393_;
}
else
{
uint8_t v_wantsRebuild_2405_; 
v_wantsRebuild_2405_ = lean_ctor_get_uint8(v_toMonitorResult_2400_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2400_);
if (v_wantsRebuild_2405_ == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v_out_2401_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v_out_2401_, 1);
v___y_2394_ = v_a_2406_;
goto v___jp_2393_;
}
else
{
uint8_t v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref_known(v_out_2401_, 1);
v___x_2407_ = 3;
v___x_2408_ = lean_io_exit(v___x_2407_);
return v___x_2408_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v_toMonitorResult_2400_);
lean_dec_ref(v_cfg_2388_);
v_a_2409_ = lean_ctor_get(v_out_2401_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_out_2401_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v_out_2401_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v_out_2401_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 0);
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2421_, lean_object* v_bctx_2422_, lean_object* v_mctx_2423_, lean_object* v_result_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2421_, v_bctx_2422_, v_mctx_2423_, v_result_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2427_, lean_object* v_cfg_2428_, lean_object* v_bctx_2429_, lean_object* v_mctx_2430_, lean_object* v_result_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2428_, v_bctx_2429_, v_mctx_2430_, v_result_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_cfg_2435_, lean_object* v_bctx_2436_, lean_object* v_mctx_2437_, lean_object* v_result_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2434_, v_cfg_2435_, v_bctx_2436_, v_mctx_2437_, v_result_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2441_, lean_object* v_build_2442_, lean_object* v_cfg_2443_, lean_object* v_caption_2444_){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_cancelTk_x3f_2449_; uint8_t v_failFast_2455_; 
v___x_2446_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2447_ = lean_st_mk_ref(v___x_2446_);
v_failFast_2455_ = lean_ctor_get_uint8(v_cfg_2443_, sizeof(void*)*5 + 3);
if (v_failFast_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_box(0);
v_cancelTk_x3f_2449_ = v___x_2456_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = l_IO_CancelToken_new();
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
v_cancelTk_x3f_2449_ = v___x_2458_;
goto v___jp_2448_;
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_inc(v_cancelTk_x3f_2449_);
lean_inc(v___x_2447_);
v___x_2450_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2443_, v___x_2447_, v_cancelTk_x3f_2449_);
lean_inc_ref(v_cfg_2443_);
v___x_2451_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2441_, v_cfg_2443_, v___x_2447_, v_cancelTk_x3f_2449_);
v___x_2452_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2451_, v_build_2442_, v_caption_2444_);
v___x_2453_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2450_, v___x_2452_);
v___x_2454_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2443_, v___x_2451_, v___x_2450_, v___x_2453_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2459_, lean_object* v_build_2460_, lean_object* v_cfg_2461_, lean_object* v_caption_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2459_, v_build_2460_, v_cfg_2461_, v_caption_2462_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2465_, lean_object* v_ws_2466_, lean_object* v_build_2467_, lean_object* v_cfg_2468_, lean_object* v_caption_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2466_, v_build_2467_, v_cfg_2468_, v_caption_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_ws_2473_, lean_object* v_build_2474_, lean_object* v_cfg_2475_, lean_object* v_caption_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2472_, v_ws_2473_, v_build_2474_, v_cfg_2475_, v_caption_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2482_, lean_object* v_job_2483_){
_start:
{
lean_object* v___x_2485_; lean_object* v_out_2486_; 
v___x_2485_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2482_, v_job_2483_);
v_out_2486_ = lean_ctor_get(v___x_2485_, 1);
lean_inc_ref(v_out_2486_);
if (lean_obj_tag(v_out_2486_) == 0)
{
lean_object* v_toMonitorResult_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2502_; 
v_toMonitorResult_2487_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v___x_2485_, 1);
lean_dec(v_unused_2503_);
v___x_2489_ = v___x_2485_;
v_isShared_2490_ = v_isSharedCheck_2502_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_toMonitorResult_2487_);
lean_dec(v___x_2485_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2502_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2501_; 
v_a_2491_ = lean_ctor_get(v_out_2486_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_out_2486_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2493_ = v_out_2486_;
v_isShared_2494_ = v_isSharedCheck_2501_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v_out_2486_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2501_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2498_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2496_);
v___x_2498_ = v___x_2489_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_toMonitorResult_2487_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2527_; 
v_a_2504_ = lean_ctor_get(v_out_2486_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_out_2486_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2506_ = v_out_2486_;
v_isShared_2507_ = v_isSharedCheck_2527_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v_out_2486_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2527_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v_toMonitorResult_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2525_; 
v_toMonitorResult_2508_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2485_, 1);
lean_dec(v_unused_2526_);
v___x_2510_ = v___x_2485_;
v_isShared_2511_ = v_isSharedCheck_2525_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_toMonitorResult_2508_);
lean_dec(v___x_2485_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2525_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_task_2512_; lean_object* v___x_2513_; 
v_task_2512_ = lean_ctor_get(v_a_2504_, 0);
lean_inc_ref(v_task_2512_);
lean_dec(v_a_2504_);
v___x_2513_ = lean_io_wait(v_task_2512_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 2);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v_a_2514_);
v___x_2516_ = v___x_2506_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2516_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v___x_2516_);
v___x_2518_ = v___x_2510_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_toMonitorResult_2508_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec_ref_known(v___x_2513_, 2);
lean_del_object(v___x_2506_);
v___x_2521_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v___x_2521_);
v___x_2523_ = v___x_2510_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_toMonitorResult_2508_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2528_, lean_object* v_job_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2528_, v_job_2529_);
lean_dec_ref(v_mctx_2528_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2532_, lean_object* v_mctx_2533_, lean_object* v_job_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2533_, v_job_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_mctx_2538_, lean_object* v_job_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2537_, v_mctx_2538_, v_job_2539_);
lean_dec_ref(v_mctx_2538_);
return v_res_2541_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2556_, lean_object* v_build_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_out_2570_; 
v___x_2559_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2560_ = lean_st_mk_ref(v___x_2559_);
v___x_2561_ = 0;
v___x_2562_ = 1;
v___x_2563_ = lean_box(0);
v___x_2564_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2560_);
v___x_2565_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2564_, v___x_2560_, v___x_2563_);
v___x_2566_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2556_, v___x_2564_, v___x_2560_, v___x_2563_);
v___x_2567_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2568_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2566_, v_build_2557_, v___x_2567_);
lean_dec_ref(v___x_2566_);
v___x_2569_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2565_, v___x_2568_);
lean_dec_ref(v___x_2565_);
v_out_2570_ = lean_ctor_get(v___x_2569_, 1);
lean_inc_ref(v_out_2570_);
lean_dec_ref(v___x_2569_);
if (lean_obj_tag(v_out_2570_) == 0)
{
lean_dec_ref_known(v_out_2570_, 1);
return v___x_2561_;
}
else
{
lean_dec_ref_known(v_out_2570_, 1);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2571_, lean_object* v_build_2572_, lean_object* v_a_2573_){
_start:
{
uint8_t v_res_2574_; lean_object* v_r_2575_; 
v_res_2574_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2571_, v_build_2572_);
v_r_2575_ = lean_box(v_res_2574_);
return v_r_2575_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2576_, lean_object* v_ws_2577_, lean_object* v_build_2578_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2577_, v_build_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_ws_2582_, lean_object* v_build_2583_, lean_object* v_a_2584_){
_start:
{
uint8_t v_res_2585_; lean_object* v_r_2586_; 
v_res_2585_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2581_, v_ws_2582_, v_build_2583_);
v_r_2586_ = lean_box(v_res_2585_);
return v_r_2586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2587_, lean_object* v_build_2588_, lean_object* v_cfg_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_cancelTk_x3f_2594_; uint8_t v_failFast_2601_; 
v___x_2591_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2592_ = lean_st_mk_ref(v___x_2591_);
v_failFast_2601_ = lean_ctor_get_uint8(v_cfg_2589_, sizeof(void*)*5 + 3);
if (v_failFast_2601_ == 0)
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_box(0);
v_cancelTk_x3f_2594_ = v___x_2602_;
goto v___jp_2593_;
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = l_IO_CancelToken_new();
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
v_cancelTk_x3f_2594_ = v___x_2604_;
goto v___jp_2593_;
}
v___jp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_inc(v_cancelTk_x3f_2594_);
lean_inc(v___x_2592_);
v___x_2595_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2589_, v___x_2592_, v_cancelTk_x3f_2594_);
lean_inc_ref(v_cfg_2589_);
v___x_2596_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2587_, v_cfg_2589_, v___x_2592_, v_cancelTk_x3f_2594_);
v___x_2597_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2598_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2596_, v_build_2588_, v___x_2597_);
v___x_2599_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2595_, v___x_2598_);
v___x_2600_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2589_, v___x_2596_, v___x_2595_, v___x_2599_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2605_, lean_object* v_build_2606_, lean_object* v_cfg_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lake_Workspace_runBuild___redArg(v_ws_2605_, v_build_2606_, v_cfg_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2610_, lean_object* v_ws_2611_, lean_object* v_build_2612_, lean_object* v_cfg_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lake_Workspace_runBuild___redArg(v_ws_2611_, v_build_2612_, v_cfg_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_ws_2617_, lean_object* v_build_2618_, lean_object* v_cfg_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lake_Workspace_runBuild(v_00_u03b1_2616_, v_ws_2617_, v_build_2618_, v_cfg_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2622_, lean_object* v_cfg_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2626_; 
lean_inc(v_a_2624_);
v___x_2626_ = l_Lake_Workspace_runBuild___redArg(v_a_2624_, v_build_2622_, v_cfg_2623_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2627_, lean_object* v_cfg_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lake_runBuild___redArg(v_build_2627_, v_cfg_2628_, v_a_2629_);
lean_dec(v_a_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2632_, lean_object* v_build_2633_, lean_object* v_cfg_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___x_2637_; 
lean_inc(v_a_2635_);
v___x_2637_ = l_Lake_Workspace_runBuild___redArg(v_a_2635_, v_build_2633_, v_cfg_2634_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_build_2639_, lean_object* v_cfg_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lake_runBuild(v_00_u03b1_2638_, v_build_2639_, v_cfg_2640_, v_a_2641_);
lean_dec(v_a_2641_);
return v_res_2643_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Index(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Run(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
