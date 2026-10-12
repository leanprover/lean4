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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object* v_out_36_, uint8_t v_outLv_37_, uint8_t v_useAnsi_38_, lean_object* v_e_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_logToStream(v_e_39_, v_out_36_, v_outLv_37_, v_useAnsi_38_);
return v___x_41_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_36_ = stack[0].m_obj;
uint8_t v_outLv_37_ = stack[1].m_num;
uint8_t v_useAnsi_38_ = stack[2].m_num;
lean_object* v_e_39_ = stack[3].m_obj;
lean_object* v_res_42_;
v_res_42_ = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(v_out_36_, v_outLv_37_, v_useAnsi_38_, v_e_39_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object* v_out_43_, lean_object* v_outLv_44_, lean_object* v_useAnsi_45_, lean_object* v_e_46_, lean_object* v___y_47_){
_start:
{
uint8_t v_outLv_boxed_48_; uint8_t v_useAnsi_boxed_49_; lean_object* v_res_50_; 
v_outLv_boxed_48_ = lean_unbox(v_outLv_44_);
v_useAnsi_boxed_49_ = lean_unbox(v_useAnsi_45_);
v_res_50_ = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(v_out_43_, v_outLv_boxed_48_, v_useAnsi_boxed_49_, v_e_46_);
lean_dec_ref(v_e_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object* v_ctx_51_){
_start:
{
lean_object* v_out_52_; uint8_t v_outLv_53_; uint8_t v_useAnsi_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___f_57_; 
v_out_52_ = lean_ctor_get(v_ctx_51_, 1);
lean_inc_ref(v_out_52_);
v_outLv_53_ = lean_ctor_get_uint8(v_ctx_51_, sizeof(void*)*4);
v_useAnsi_54_ = lean_ctor_get_uint8(v_ctx_51_, sizeof(void*)*4 + 4);
lean_dec_ref(v_ctx_51_);
v___x_55_ = lean_box(v_outLv_53_);
v___x_56_ = lean_box(v_useAnsi_54_);
v___f_57_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed), 5, 3);
lean_closure_set(v___f_57_, 0, v_out_52_);
lean_closure_set(v___f_57_, 1, v___x_55_);
lean_closure_set(v___f_57_, 2, v___x_56_);
return v___f_57_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* v_ctx_58_, lean_object* v_s_59_, lean_object* v_self_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_apply_3(v_self_60_, v_ctx_58_, v_s_59_, lean_box(0));
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_58_ = stack[0].m_obj;
lean_object* v_s_59_ = stack[1].m_obj;
lean_object* v_self_60_ = stack[2].m_obj;
lean_object* v_res_63_;
v_res_63_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(v_ctx_58_, v_s_59_, v_self_60_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object* v_ctx_64_, lean_object* v_s_65_, lean_object* v_self_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(v_ctx_64_, v_s_65_, v_self_66_);
return v_res_68_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* v_00_u03b1_69_, lean_object* v_ctx_70_, lean_object* v_s_71_, lean_object* v_self_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_apply_3(v_self_72_, v_ctx_70_, v_s_71_, lean_box(0));
return v___x_74_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_MonitorM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_70_ = stack[1].m_obj;
lean_object* v_s_71_ = stack[2].m_obj;
lean_object* v_self_72_ = stack[3].m_obj;
lean_object* v_res_75_;
v_res_75_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_box(0), v_ctx_70_, v_s_71_, v_self_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object* v_00_u03b1_76_, lean_object* v_ctx_77_, lean_object* v_s_78_, lean_object* v_self_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run(v_00_u03b1_76_, v_ctx_77_, v_s_78_, v_self_79_);
return v_res_81_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* v_out_84_){
_start:
{
lean_object* v_flush_86_; lean_object* v___x_87_; 
v_flush_86_ = lean_ctor_get(v_out_84_, 0);
lean_inc_ref(v_flush_86_);
lean_dec_ref(v_out_84_);
v___x_87_ = lean_apply_1(v_flush_86_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
return v_a_88_;
}
else
{
lean_object* v___x_89_; 
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_flush_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_84_ = stack[0].m_obj;
lean_object* v_res_90_;
v_res_90_ = l___private_Lake_Build_Run_0__Lake_flush(v_out_84_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object* v_out_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lake_Build_Run_0__Lake_flush(v_out_91_);
return v_res_93_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = l_instMonadBaseIO;
v___x_96_ = l_instInhabitedOfMonad___redArg(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16(void){
_start:
{
uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = 1;
v___x_127_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__16, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16);
v___x_130_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_131_ = lean_string_append(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_134_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__17, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
v___x_135_ = lean_string_append(v___x_134_, v___x_133_);
return v___x_135_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* v_out_137_, lean_object* v_s_138_){
_start:
{
lean_object* v_putStr_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_putStr_140_ = lean_ctor_get(v_out_137_, 4);
lean_inc_ref(v_putStr_140_);
lean_dec_ref(v_out_137_);
v___x_141_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
lean_inc_ref(v_s_138_);
v___x_142_ = lean_apply_2(v_putStr_140_, v_s_138_, lean_box(0));
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; 
lean_dec_ref(v_s_138_);
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_142_, 1);
return v_a_143_;
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_168_; 
v_a_144_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_168_ == 0)
{
v___x_146_ = v___x_142_;
v_isShared_147_ = v_isSharedCheck_168_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_168_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_148_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_149_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_150_ = lean_unsigned_to_nat(82u);
v___x_151_ = lean_unsigned_to_nat(4u);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_154_ = lean_io_error_to_string(v_a_144_);
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
v___x_158_ = l_String_quote(v_s_138_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 3);
lean_ctor_set(v___x_146_, 0, v___x_158_);
v___x_160_ = v___x_146_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_167_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_186__overap_165_; lean_object* v___x_166_; 
v___x_161_ = l_Std_Format_defWidth;
v___x_162_ = l_Std_Format_pretty(v___x_160_, v___x_161_, v___x_152_, v___x_152_);
v___x_163_ = lean_string_append(v___x_157_, v___x_162_);
lean_dec_ref(v___x_162_);
v___x_164_ = l_mkPanicMessageWithDecl(v___x_148_, v___x_149_, v___x_150_, v___x_151_, v___x_163_);
lean_dec_ref(v___x_163_);
v___x_186__overap_165_ = l_panic___redArg(v___x_141_, v___x_164_);
v___x_166_ = lean_apply_1(v___x_186__overap_165_, lean_box(0));
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_print_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_137_ = stack[0].m_obj;
lean_object* v_s_138_ = stack[1].m_obj;
lean_object* v_res_169_;
v_res_169_ = l___private_Lake_Build_Run_0__Lake_print_x21(v_out_137_, v_s_138_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object* v_out_170_, lean_object* v_s_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lake_Build_Run_0__Lake_print_x21(v_out_170_, v_s_171_);
return v_res_173_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* v_s_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_val_179_; lean_object* v_out_181_; lean_object* v_putStr_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_out_181_ = lean_ctor_get(v_a_175_, 1);
v_putStr_182_ = lean_ctor_get(v_out_181_, 4);
v___x_183_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
lean_inc_ref(v_putStr_182_);
lean_inc_ref(v_s_174_);
v___x_184_ = lean_apply_2(v_putStr_182_, v_s_174_, lean_box(0));
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; 
lean_dec_ref(v_s_174_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v_val_179_ = v_a_185_;
goto v___jp_178_;
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_210_; 
v_a_186_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_210_ == 0)
{
v___x_188_ = v___x_184_;
v_isShared_189_ = v_isSharedCheck_210_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_210_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_190_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_191_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_192_ = lean_unsigned_to_nat(82u);
v___x_193_ = lean_unsigned_to_nat(4u);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_196_ = lean_io_error_to_string(v_a_186_);
v___x_197_ = lean_string_append(v___x_195_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_199_ = lean_string_append(v___x_197_, v___x_198_);
v___x_200_ = l_String_quote(v_s_174_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 3);
lean_ctor_set(v___x_188_, 0, v___x_200_);
v___x_202_ = v___x_188_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_209_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_1132__overap_207_; lean_object* v___x_208_; 
v___x_203_ = l_Std_Format_defWidth;
v___x_204_ = l_Std_Format_pretty(v___x_202_, v___x_203_, v___x_194_, v___x_194_);
v___x_205_ = lean_string_append(v___x_199_, v___x_204_);
lean_dec_ref(v___x_204_);
v___x_206_ = l_mkPanicMessageWithDecl(v___x_190_, v___x_191_, v___x_192_, v___x_193_, v___x_205_);
lean_dec_ref(v___x_205_);
v___x_1132__overap_207_ = l_panic___redArg(v___x_183_, v___x_206_);
v___x_208_ = lean_apply_1(v___x_1132__overap_207_, lean_box(0));
v_val_179_ = v___x_208_;
goto v___jp_178_;
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_val_179_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
return v___x_180_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_print_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_174_ = stack[0].m_obj;
lean_object* v_a_175_ = stack[1].m_obj;
lean_object* v_a_176_ = stack[2].m_obj;
lean_object* v_res_211_;
v_res_211_ = l___private_Lake_Build_Run_0__Lake_Monitor_print(v_s_174_, v_a_175_, v_a_176_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object* v_s_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_Lake_Build_Run_0__Lake_Monitor_print(v_s_212_, v_a_213_, v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_216_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_val_221_; lean_object* v_out_223_; lean_object* v_flush_224_; lean_object* v___x_225_; 
v_out_223_ = lean_ctor_get(v_a_217_, 1);
v_flush_224_ = lean_ctor_get(v_out_223_, 0);
lean_inc_ref(v_flush_224_);
v___x_225_ = lean_apply_1(v_flush_224_, lean_box(0));
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v_val_221_ = v_a_226_;
goto v___jp_220_;
}
else
{
lean_object* v___x_227_; 
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = lean_box(0);
v_val_221_ = v___x_227_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_val_221_);
lean_ctor_set(v___x_222_, 1, v_a_218_);
return v___x_222_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_flush_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_217_ = stack[0].m_obj;
lean_object* v_a_218_ = stack[1].m_obj;
lean_object* v_res_228_;
v_res_228_ = l___private_Lake_Build_Run_0__Lake_Monitor_flush(v_a_217_, v_a_218_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lake_Build_Run_0__Lake_Monitor_flush(v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_232_;
}
}
lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* v_msg_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_7771__overap_236_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_7771__overap_236_ = lean_panic_fn_borrowed(v___x_235_, v_msg_233_);
v___x_237_ = lean_apply_1(v___x_7771__overap_236_, lean_box(0));
return v___x_237_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_233_ = stack[0].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v_msg_233_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object* v_msg_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v_msg_239_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_243_ = lean_array_get_size(v___x_242_);
return v___x_243_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* v_running_250_, lean_object* v_unfinished_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
uint8_t v_showProgress_258_; 
v_showProgress_258_ = lean_ctor_get_uint8(v_a_252_, sizeof(void*)*4 + 5);
if (v_showProgress_258_ == 0)
{
goto v___jp_255_;
}
else
{
uint8_t v_useAnsi_259_; 
v_useAnsi_259_ = lean_ctor_get_uint8(v_a_252_, sizeof(void*)*4 + 4);
if (v_useAnsi_259_ == 0)
{
goto v___jp_255_;
}
else
{
lean_object* v_jobNo_260_; lean_object* v_totalJobs_261_; uint8_t v_wantsRebuild_262_; lean_object* v_failures_263_; lean_object* v_resetCtrl_264_; lean_object* v_lastUpdate_265_; lean_object* v_spinnerIdx_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_355_; 
v_jobNo_260_ = lean_ctor_get(v_a_253_, 0);
v_totalJobs_261_ = lean_ctor_get(v_a_253_, 1);
v_wantsRebuild_262_ = lean_ctor_get_uint8(v_a_253_, sizeof(void*)*6);
v_failures_263_ = lean_ctor_get(v_a_253_, 2);
v_resetCtrl_264_ = lean_ctor_get(v_a_253_, 3);
v_lastUpdate_265_ = lean_ctor_get(v_a_253_, 4);
v_spinnerIdx_266_ = lean_ctor_get(v_a_253_, 5);
v_isSharedCheck_355_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_355_ == 0)
{
v___x_268_ = v_a_253_;
v_isShared_269_ = v_isSharedCheck_355_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_spinnerIdx_266_);
lean_inc(v_lastUpdate_265_);
lean_inc(v_resetCtrl_264_);
lean_inc(v_failures_263_);
lean_inc(v_totalJobs_261_);
lean_inc(v_jobNo_260_);
lean_dec(v_a_253_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_355_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_out_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_out_270_ = lean_ctor_get(v_a_252_, 1);
v___x_271_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
v___x_272_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
v___x_273_ = lean_array_fget_borrowed(v___x_271_, v_spinnerIdx_266_);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = l_Fin_add(v___x_272_, v_spinnerIdx_266_, v___x_274_);
lean_dec(v_spinnerIdx_266_);
v___x_276_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(v_totalJobs_261_);
lean_inc(v_jobNo_260_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 5, v___x_275_);
lean_ctor_set(v___x_268_, 3, v___x_276_);
v___x_278_ = v___x_268_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_jobNo_260_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_totalJobs_261_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_failures_263_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_lastUpdate_265_);
lean_ctor_set(v_reuseFailAlloc_354_, 5, v___x_275_);
lean_ctor_set_uint8(v_reuseFailAlloc_354_, sizeof(void*)*6, v_wantsRebuild_262_);
v___x_278_ = v_reuseFailAlloc_354_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v_val_280_; lean_object* v___y_288_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_array_get_size(v_running_250_);
v___x_336_ = lean_nat_dec_lt(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_caption_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = lean_array_get_size(v_unfinished_251_);
v___x_338_ = lean_nat_sub(v___x_337_, v___x_274_);
v___x_339_ = lean_array_fget_borrowed(v_unfinished_251_, v___x_338_);
lean_dec(v___x_338_);
v_caption_340_ = lean_ctor_get(v___x_339_, 2);
v___x_341_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_342_ = lean_string_append(v___x_341_, v_caption_340_);
v___y_288_ = v___x_342_;
goto v___jp_287_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_caption_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_343_ = lean_nat_sub(v___x_335_, v___x_274_);
v___x_344_ = lean_array_fget_borrowed(v_running_250_, v___x_343_);
v_caption_345_ = lean_ctor_get(v___x_344_, 2);
v___x_346_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
v___x_347_ = lean_string_append(v___x_346_, v_caption_345_);
v___x_348_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
v___x_350_ = l_Nat_reprFast(v___x_343_);
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___y_288_ = v___x_353_;
goto v___jp_287_;
}
v___jp_279_:
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_val_280_);
lean_ctor_set(v___x_281_, 1, v___x_278_);
return v___x_281_;
}
v___jp_282_:
{
lean_object* v_flush_283_; lean_object* v___x_284_; 
v_flush_283_ = lean_ctor_get(v_out_270_, 0);
lean_inc_ref(v_flush_283_);
v___x_284_ = lean_apply_1(v_flush_283_, lean_box(0));
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v_val_280_ = v_a_285_;
goto v___jp_279_;
}
else
{
lean_object* v___x_286_; 
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = lean_box(0);
v_val_280_ = v___x_286_;
goto v___jp_279_;
}
}
v___jp_287_:
{
lean_object* v_putStr_289_; lean_object* v___x_290_; uint32_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_putStr_289_ = lean_ctor_get(v_out_270_, 4);
v___x_290_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_291_ = lean_unbox_uint32(v___x_273_);
v___x_292_ = lean_string_push(v___x_290_, v___x_291_);
v___x_293_ = lean_string_append(v_resetCtrl_264_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
v___x_296_ = l_Nat_reprFast(v_jobNo_260_);
v___x_297_ = lean_string_append(v___x_295_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = l_Nat_reprFast(v_totalJobs_261_);
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v___x_304_ = lean_string_append(v___x_303_, v___y_288_);
lean_dec_ref(v___y_288_);
lean_inc_ref(v_putStr_289_);
lean_inc_ref(v___x_304_);
v___x_305_ = lean_apply_2(v_putStr_289_, v___x_304_, lean_box(0));
if (lean_obj_tag(v___x_305_) == 0)
{
lean_dec_ref_known(v___x_305_, 1);
lean_dec_ref(v___x_304_);
goto v___jp_282_;
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_333_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_333_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_333_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_333_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_310_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_311_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_312_ = lean_unsigned_to_nat(82u);
v___x_313_ = lean_unsigned_to_nat(4u);
v___x_314_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_317_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_316_, v_useAnsi_259_);
v___x_318_ = lean_string_append(v___x_314_, v___x_317_);
lean_dec_ref(v___x_317_);
v___x_319_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_320_ = lean_string_append(v___x_318_, v___x_319_);
v___x_321_ = lean_io_error_to_string(v_a_306_);
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = lean_string_append(v___x_322_, v___x_302_);
v___x_324_ = l_String_quote(v___x_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 3);
lean_ctor_set(v___x_308_, 0, v___x_324_);
v___x_326_ = v___x_308_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_332_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = l_Std_Format_defWidth;
v___x_328_ = l_Std_Format_pretty(v___x_326_, v___x_327_, v___x_315_, v___x_315_);
v___x_329_ = lean_string_append(v___x_323_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = l_mkPanicMessageWithDecl(v___x_310_, v___x_311_, v___x_312_, v___x_313_, v___x_329_);
lean_dec_ref(v___x_329_);
v___x_331_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_330_);
goto v___jp_282_;
}
}
}
}
}
}
}
}
v___jp_255_:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_a_253_);
return v___x_257_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_running_250_ = stack[0].m_obj;
lean_object* v_unfinished_251_ = stack[1].m_obj;
lean_object* v_a_252_ = stack[2].m_obj;
lean_object* v_a_253_ = stack[3].m_obj;
lean_object* v_res_356_;
v_res_356_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_250_, v_unfinished_251_, v_a_252_, v_a_253_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* v_running_357_, lean_object* v_unfinished_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_357_, v_unfinished_358_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_unfinished_358_);
lean_dec_ref(v_running_357_);
return v_res_362_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* v_running_363_, lean_object* v_unfinished_364_, lean_object* v_h_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_running_363_, v_unfinished_364_, v_a_366_, v_a_367_);
return v___x_369_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress_0interp(lean_interpreter_value* stack)
{
lean_object* v_running_363_ = stack[0].m_obj;
lean_object* v_unfinished_364_ = stack[1].m_obj;
lean_object* v_a_366_ = stack[3].m_obj;
lean_object* v_a_367_ = stack[4].m_obj;
lean_object* v_res_370_;
v_res_370_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(v_running_363_, v_unfinished_364_, lean_box(0), v_a_366_, v_a_367_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* v_running_371_, lean_object* v_unfinished_372_, lean_object* v_h_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(v_running_371_, v_unfinished_372_, v_h_373_, v_a_374_, v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_unfinished_372_);
lean_dec_ref(v_running_371_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object* v_ms_381_){
_start:
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(10000u);
v___x_383_ = lean_nat_dec_lt(v___x_382_, v_ms_381_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1000u);
v___x_385_ = lean_nat_dec_lt(v___x_384_, v_ms_381_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = l_Nat_reprFast(v_ms_381_);
v___x_387_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_389_ = lean_nat_div(v_ms_381_, v___x_384_);
v___x_390_ = l_Nat_reprFast(v___x_389_);
v___x_391_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1));
v___x_392_ = lean_string_append(v___x_390_, v___x_391_);
v___x_393_ = lean_unsigned_to_nat(50u);
v___x_394_ = lean_nat_add(v_ms_381_, v___x_393_);
lean_dec(v_ms_381_);
v___x_395_ = lean_unsigned_to_nat(100u);
v___x_396_ = lean_nat_div(v___x_394_, v___x_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_unsigned_to_nat(10u);
v___x_398_ = lean_nat_mod(v___x_396_, v___x_397_);
lean_dec(v___x_396_);
v___x_399_ = l_Nat_reprFast(v___x_398_);
v___x_400_ = lean_string_append(v___x_392_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
return v___x_402_;
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_403_ = lean_unsigned_to_nat(1000u);
v___x_404_ = lean_nat_div(v_ms_381_, v___x_403_);
lean_dec(v_ms_381_);
v___x_405_ = l_Nat_reprFast(v___x_404_);
v___x_406_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
v___x_407_ = lean_string_append(v___x_405_, v___x_406_);
return v___x_407_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* v_out_408_, uint8_t v___y_409_, uint8_t v_useAnsi_410_, lean_object* v_as_411_, size_t v_i_412_, size_t v_stop_413_, lean_object* v_b_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_eq(v_i_412_, v_stop_413_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; size_t v___x_420_; size_t v___x_421_; 
v___x_418_ = lean_array_uget_borrowed(v_as_411_, v_i_412_);
lean_inc_ref(v_out_408_);
v___x_419_ = l_Lake_logToStream(v___x_418_, v_out_408_, v___y_409_, v_useAnsi_410_);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_i_412_, v___x_420_);
v_i_412_ = v___x_421_;
v_b_414_ = v___x_419_;
goto _start;
}
else
{
lean_object* v___x_423_; 
lean_dec_ref(v_out_408_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_b_414_);
lean_ctor_set(v___x_423_, 1, v___y_415_);
return v___x_423_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_408_ = stack[0].m_obj;
uint8_t v___y_409_ = stack[1].m_num;
uint8_t v_useAnsi_410_ = stack[2].m_num;
lean_object* v_as_411_ = stack[3].m_obj;
size_t v_i_412_ = stack[4].m_num;
size_t v_stop_413_ = stack[5].m_num;
lean_object* v_b_414_ = stack[6].m_obj;
lean_object* v___y_415_ = stack[7].m_obj;
lean_object* v_res_424_;
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_408_, v___y_409_, v_useAnsi_410_, v_as_411_, v_i_412_, v_stop_413_, v_b_414_, v___y_415_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* v_out_425_, lean_object* v___y_426_, lean_object* v_useAnsi_427_, lean_object* v_as_428_, lean_object* v_i_429_, lean_object* v_stop_430_, lean_object* v_b_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___y_14248__boxed_434_; uint8_t v_useAnsi_14249__boxed_435_; size_t v_i_boxed_436_; size_t v_stop_boxed_437_; lean_object* v_res_438_; 
v___y_14248__boxed_434_ = lean_unbox(v___y_426_);
v_useAnsi_14249__boxed_435_ = lean_unbox(v_useAnsi_427_);
v_i_boxed_436_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_stop_boxed_437_ = lean_unbox_usize(v_stop_430_);
lean_dec(v_stop_430_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_425_, v___y_14248__boxed_434_, v_useAnsi_14249__boxed_435_, v_as_428_, v_i_boxed_436_, v_stop_boxed_437_, v_b_431_, v___y_432_);
lean_dec_ref(v_as_428_);
return v_res_438_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___y_453_; lean_object* v_val_454_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_465_; lean_object* v_jobNo_468_; lean_object* v_totalJobs_469_; uint8_t v_wantsRebuild_470_; lean_object* v_failures_471_; lean_object* v_resetCtrl_472_; lean_object* v_lastUpdate_473_; lean_object* v_spinnerIdx_474_; lean_object* v_out_475_; uint8_t v_outLv_476_; uint8_t v_failLv_477_; uint8_t v_minAction_478_; uint8_t v_showOptional_479_; uint8_t v_useAnsi_480_; uint8_t v_showProgress_481_; uint8_t v_showTime_482_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; uint8_t v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_570_; lean_object* v___y_571_; uint8_t v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; uint8_t v___y_576_; lean_object* v___y_577_; uint8_t v___y_578_; lean_object* v___y_579_; lean_object* v_task_581_; lean_object* v_caption_582_; uint8_t v_optional_583_; uint8_t v___y_585_; uint8_t v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; uint8_t v___y_589_; uint8_t v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; uint32_t v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; uint8_t v___y_597_; lean_object* v___y_598_; uint8_t v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; uint8_t v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; uint32_t v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; uint8_t v___y_637_; lean_object* v___y_638_; uint8_t v___y_639_; lean_object* v___y_640_; uint8_t v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint32_t v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; lean_object* v___y_650_; uint8_t v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; uint32_t v___y_670_; lean_object* v___y_674_; lean_object* v___y_675_; uint8_t v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; uint8_t v___y_681_; uint8_t v___y_682_; uint8_t v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; lean_object* v___y_703_; lean_object* v___y_704_; uint8_t v___y_705_; uint8_t v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; uint8_t v___y_711_; uint8_t v___y_712_; lean_object* v___y_713_; uint8_t v___y_714_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_730_; lean_object* v___y_731_; uint8_t v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; uint8_t v___y_739_; uint8_t v___y_740_; uint8_t v___y_742_; uint8_t v___y_743_; lean_object* v___y_744_; uint8_t v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; uint8_t v___y_770_; uint8_t v___y_771_; lean_object* v___y_772_; uint8_t v___y_773_; uint8_t v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; uint8_t v___y_777_; lean_object* v___y_778_; uint8_t v___y_779_; uint8_t v___y_794_; uint8_t v___y_795_; uint8_t v___y_796_; lean_object* v___y_797_; uint8_t v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; uint8_t v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; uint8_t v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_820_; lean_object* v___x_832_; lean_object* v_a_833_; 
v_jobNo_468_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_jobNo_468_);
v_totalJobs_469_ = lean_ctor_get(v_a_450_, 1);
lean_inc(v_totalJobs_469_);
v_wantsRebuild_470_ = lean_ctor_get_uint8(v_a_450_, sizeof(void*)*6);
v_failures_471_ = lean_ctor_get(v_a_450_, 2);
v_resetCtrl_472_ = lean_ctor_get(v_a_450_, 3);
v_lastUpdate_473_ = lean_ctor_get(v_a_450_, 4);
v_spinnerIdx_474_ = lean_ctor_get(v_a_450_, 5);
v_out_475_ = lean_ctor_get(v_a_449_, 1);
v_outLv_476_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4);
v_failLv_477_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4 + 1);
v_minAction_478_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4 + 2);
v_showOptional_479_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4 + 3);
v_useAnsi_480_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4 + 4);
v_showProgress_481_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4 + 5);
v_showTime_482_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*4 + 6);
v_task_581_ = lean_ctor_get(v_job_448_, 0);
lean_inc_ref(v_task_581_);
v_caption_582_ = lean_ctor_get(v_job_448_, 2);
lean_inc_ref(v_caption_582_);
v_optional_583_ = lean_ctor_get_uint8(v_job_448_, sizeof(void*)*3);
lean_dec_ref(v_job_448_);
v___x_832_ = lean_task_get_own(v_task_581_);
v_a_833_ = lean_ctor_get(v___x_832_, 1);
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___y_820_ = v_a_833_;
goto v___jp_819_;
v___jp_452_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_val_454_);
lean_ctor_set(v___x_455_, 1, v___y_453_);
return v___x_455_;
}
v___jp_456_:
{
lean_object* v_out_459_; lean_object* v_flush_460_; lean_object* v___x_461_; 
v_out_459_ = lean_ctor_get(v___y_457_, 1);
v_flush_460_ = lean_ctor_get(v_out_459_, 0);
lean_inc_ref(v_flush_460_);
v___x_461_ = lean_apply_1(v_flush_460_, lean_box(0));
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___y_453_ = v___y_458_;
v_val_454_ = v_a_462_;
goto v___jp_452_;
}
else
{
lean_object* v___x_463_; 
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_box(0);
v___y_453_ = v___y_458_;
v_val_454_ = v___x_463_;
goto v___jp_452_;
}
}
v___jp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_box(0);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___y_465_);
return v___x_467_;
}
v___jp_483_:
{
uint8_t v___x_490_; 
v___x_490_ = lean_nat_dec_lt(v___y_488_, v___y_487_);
lean_dec(v___y_488_);
if (v___x_490_ == 0)
{
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
v___y_457_ = v___y_484_;
v___y_458_ = v___y_485_;
goto v___jp_456_;
}
else
{
lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; lean_object* v_snd_495_; 
v___x_491_ = lean_box(0);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = lean_usize_of_nat(v___y_487_);
lean_dec(v___y_487_);
lean_inc_ref(v_out_475_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_475_, v___y_489_, v_useAnsi_480_, v___y_486_, v___x_492_, v___x_493_, v___x_491_, v___y_485_);
lean_dec_ref(v___y_486_);
v_snd_495_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_snd_495_);
lean_dec_ref(v___x_494_);
v___y_457_ = v___y_484_;
v___y_458_ = v_snd_495_;
goto v___jp_456_;
}
}
v___jp_496_:
{
if (v___y_498_ == 0)
{
lean_dec(v___y_503_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
v___y_457_ = v___y_497_;
v___y_458_ = v___y_499_;
goto v___jp_456_;
}
else
{
if (v___y_502_ == 0)
{
v___y_484_ = v___y_497_;
v___y_485_ = v___y_499_;
v___y_486_ = v___y_500_;
v___y_487_ = v___y_501_;
v___y_488_ = v___y_503_;
v___y_489_ = v_outLv_476_;
goto v___jp_483_;
}
else
{
uint8_t v___x_504_; 
v___x_504_ = 0;
v___y_484_ = v___y_497_;
v___y_485_ = v___y_499_;
v___y_486_ = v___y_500_;
v___y_487_ = v___y_501_;
v___y_488_ = v___y_503_;
v___y_489_ = v___x_504_;
goto v___jp_483_;
}
}
}
v___jp_505_:
{
lean_object* v_out_515_; lean_object* v_jobNo_516_; lean_object* v_totalJobs_517_; uint8_t v_wantsRebuild_518_; lean_object* v_failures_519_; lean_object* v_resetCtrl_520_; lean_object* v_lastUpdate_521_; lean_object* v_spinnerIdx_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_568_; 
v_out_515_ = lean_ctor_get(v___y_506_, 1);
v_jobNo_516_ = lean_ctor_get(v___y_508_, 0);
v_totalJobs_517_ = lean_ctor_get(v___y_508_, 1);
v_wantsRebuild_518_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*6);
v_failures_519_ = lean_ctor_get(v___y_508_, 2);
v_resetCtrl_520_ = lean_ctor_get(v___y_508_, 3);
v_lastUpdate_521_ = lean_ctor_get(v___y_508_, 4);
v_spinnerIdx_522_ = lean_ctor_get(v___y_508_, 5);
v_isSharedCheck_568_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_568_ == 0)
{
v___x_524_ = v___y_508_;
v_isShared_525_ = v_isSharedCheck_568_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_spinnerIdx_522_);
lean_inc(v_lastUpdate_521_);
lean_inc(v_resetCtrl_520_);
lean_inc(v_failures_519_);
lean_inc(v_totalJobs_517_);
lean_inc(v_jobNo_516_);
lean_dec(v___y_508_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_568_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_putStr_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v_putStr_526_ = lean_ctor_get(v_out_515_, 4);
v___x_527_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 3, v___x_527_);
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_jobNo_516_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_totalJobs_517_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_failures_519_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_lastUpdate_521_);
lean_ctor_set(v_reuseFailAlloc_567_, 5, v_spinnerIdx_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_567_, sizeof(void*)*6, v_wantsRebuild_518_);
v___x_529_ = v_reuseFailAlloc_567_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = lean_string_append(v_resetCtrl_520_, v___y_514_);
lean_dec_ref(v___y_514_);
v___x_531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_532_ = lean_string_append(v___x_530_, v___x_531_);
lean_inc_ref(v_putStr_526_);
lean_inc_ref(v___x_532_);
v___x_533_ = lean_apply_2(v_putStr_526_, v___x_532_, lean_box(0));
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
lean_dec_ref(v___x_532_);
v___y_497_ = v___y_506_;
v___y_498_ = v___y_507_;
v___y_499_ = v___x_529_;
v___y_500_ = v___y_509_;
v___y_501_ = v___y_510_;
v___y_502_ = v___y_511_;
v___y_503_ = v___y_513_;
goto v___jp_496_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_566_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_566_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_566_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_566_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_538_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_539_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_540_ = lean_unsigned_to_nat(82u);
v___x_541_ = lean_unsigned_to_nat(4u);
v___x_542_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_543_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_544_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc(v___y_513_);
v___x_545_ = l_Lean_Name_num___override(v___x_544_, v___y_513_);
v___x_546_ = l_Lean_Name_str___override(v___x_545_, v___x_543_);
v___x_547_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_548_ = l_Lean_Name_str___override(v___x_546_, v___x_547_);
v___x_549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_548_, v___y_512_);
v___x_550_ = lean_string_append(v___x_542_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
v___x_553_ = lean_io_error_to_string(v_a_534_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v___x_557_ = l_String_quote(v___x_532_);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 3);
lean_ctor_set(v___x_536_, 0, v___x_557_);
v___x_559_ = v___x_536_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_565_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_560_ = l_Std_Format_defWidth;
lean_inc_n(v___y_513_, 2);
v___x_561_ = l_Std_Format_pretty(v___x_559_, v___x_560_, v___y_513_, v___y_513_);
v___x_562_ = lean_string_append(v___x_556_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_563_ = l_mkPanicMessageWithDecl(v___x_538_, v___x_539_, v___x_540_, v___x_541_, v___x_562_);
lean_dec_ref(v___x_562_);
v___x_564_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_563_);
v___y_497_ = v___y_506_;
v___y_498_ = v___y_507_;
v___y_499_ = v___x_529_;
v___y_500_ = v___y_509_;
v___y_501_ = v___y_510_;
v___y_502_ = v___y_511_;
v___y_503_ = v___y_513_;
goto v___jp_496_;
}
}
}
}
}
}
v___jp_569_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lake_Ansi_chalk(v___y_579_, v___y_573_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v___y_579_);
v___y_506_ = v___y_570_;
v___y_507_ = v___y_572_;
v___y_508_ = v___y_571_;
v___y_509_ = v___y_574_;
v___y_510_ = v___y_575_;
v___y_511_ = v___y_576_;
v___y_512_ = v___y_578_;
v___y_513_ = v___y_577_;
v___y_514_ = v___x_580_;
goto v___jp_505_;
}
v___jp_584_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_599_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_600_ = lean_string_push(v___x_599_, v___y_594_);
v___x_601_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
v___x_603_ = l_Nat_reprFast(v_jobNo_468_);
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
lean_dec_ref(v___x_603_);
v___x_605_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
v___x_607_ = l_Nat_reprFast(v_totalJobs_469_);
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
lean_dec_ref(v___x_607_);
v___x_609_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
v___x_611_ = lean_string_append(v___x_610_, v___y_587_);
v___x_612_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_613_ = lean_string_append(v___x_611_, v___x_612_);
v___x_614_ = lean_string_append(v___x_613_, v___y_591_);
lean_dec_ref(v___y_591_);
v___x_615_ = lean_string_append(v___x_614_, v___x_612_);
v___x_616_ = lean_string_append(v___x_615_, v_caption_582_);
lean_dec_ref(v_caption_582_);
v___x_617_ = lean_string_append(v___x_616_, v___y_598_);
lean_dec_ref(v___y_598_);
if (v_useAnsi_480_ == 0)
{
v___y_506_ = v___y_592_;
v___y_507_ = v___y_585_;
v___y_508_ = v___y_593_;
v___y_509_ = v___y_595_;
v___y_510_ = v___y_596_;
v___y_511_ = v___y_597_;
v___y_512_ = v___y_589_;
v___y_513_ = v___y_588_;
v___y_514_ = v___x_617_;
goto v___jp_505_;
}
else
{
if (v___y_585_ == 0)
{
if (v___y_590_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
v___y_572_ = v___y_585_;
v___y_573_ = v___x_617_;
v___y_574_ = v___y_595_;
v___y_575_ = v___y_596_;
v___y_576_ = v___y_597_;
v___y_577_ = v___y_588_;
v___y_578_ = v___y_589_;
v___y_579_ = v___x_618_;
goto v___jp_569_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
v___y_572_ = v___y_585_;
v___y_573_ = v___x_617_;
v___y_574_ = v___y_595_;
v___y_575_ = v___y_596_;
v___y_576_ = v___y_597_;
v___y_577_ = v___y_588_;
v___y_578_ = v___y_589_;
v___y_579_ = v___x_619_;
goto v___jp_569_;
}
}
else
{
lean_object* v___x_620_; 
v___x_620_ = l_Lake_LogLevel_ansiColor(v___y_586_);
v___y_570_ = v___y_592_;
v___y_571_ = v___y_593_;
v___y_572_ = v___y_585_;
v___y_573_ = v___x_617_;
v___y_574_ = v___y_595_;
v___y_575_ = v___y_596_;
v___y_576_ = v___y_597_;
v___y_577_ = v___y_588_;
v___y_578_ = v___y_589_;
v___y_579_ = v___x_620_;
goto v___jp_569_;
}
}
}
v___jp_621_:
{
lean_object* v___x_635_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_585_ = v___y_622_;
v___y_586_ = v___y_623_;
v___y_587_ = v___y_624_;
v___y_588_ = v___y_625_;
v___y_589_ = v___y_626_;
v___y_590_ = v___y_627_;
v___y_591_ = v___y_628_;
v___y_592_ = v___y_629_;
v___y_593_ = v___y_630_;
v___y_594_ = v___y_631_;
v___y_595_ = v___y_632_;
v___y_596_ = v___y_633_;
v___y_597_ = v___y_634_;
v___y_598_ = v___x_635_;
goto v___jp_584_;
}
v___jp_636_:
{
if (v_showTime_482_ == 0)
{
lean_dec(v___y_638_);
v___y_622_ = v___y_637_;
v___y_623_ = v___y_639_;
v___y_624_ = v___y_650_;
v___y_625_ = v___y_640_;
v___y_626_ = v___y_641_;
v___y_627_ = v___y_642_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_646_;
v___y_632_ = v___y_647_;
v___y_633_ = v___y_648_;
v___y_634_ = v___y_649_;
goto v___jp_621_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = lean_nat_dec_lt(v___y_640_, v___y_638_);
if (v___x_651_ == 0)
{
lean_dec(v___y_638_);
v___y_622_ = v___y_637_;
v___y_623_ = v___y_639_;
v___y_624_ = v___y_650_;
v___y_625_ = v___y_640_;
v___y_626_ = v___y_641_;
v___y_627_ = v___y_642_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_646_;
v___y_632_ = v___y_647_;
v___y_633_ = v___y_648_;
v___y_634_ = v___y_649_;
goto v___jp_621_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_652_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_653_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_638_);
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
v___y_585_ = v___y_637_;
v___y_586_ = v___y_639_;
v___y_587_ = v___y_650_;
v___y_588_ = v___y_640_;
v___y_589_ = v___y_641_;
v___y_590_ = v___y_642_;
v___y_591_ = v___y_643_;
v___y_592_ = v___y_644_;
v___y_593_ = v___y_645_;
v___y_594_ = v___y_646_;
v___y_595_ = v___y_647_;
v___y_596_ = v___y_648_;
v___y_597_ = v___y_649_;
v___y_598_ = v___x_656_;
goto v___jp_584_;
}
}
}
v___jp_657_:
{
if (v_optional_583_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_637_ = v___y_658_;
v___y_638_ = v___y_659_;
v___y_639_ = v___y_660_;
v___y_640_ = v___y_661_;
v___y_641_ = v___y_662_;
v___y_642_ = v___y_663_;
v___y_643_ = v___y_664_;
v___y_644_ = v___y_665_;
v___y_645_ = v___y_666_;
v___y_646_ = v___y_670_;
v___y_647_ = v___y_667_;
v___y_648_ = v___y_668_;
v___y_649_ = v___y_669_;
v___y_650_ = v___x_671_;
goto v___jp_636_;
}
else
{
lean_object* v___x_672_; 
v___x_672_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__7));
v___y_637_ = v___y_658_;
v___y_638_ = v___y_659_;
v___y_639_ = v___y_660_;
v___y_640_ = v___y_661_;
v___y_641_ = v___y_662_;
v___y_642_ = v___y_663_;
v___y_643_ = v___y_664_;
v___y_644_ = v___y_665_;
v___y_645_ = v___y_666_;
v___y_646_ = v___y_670_;
v___y_647_ = v___y_667_;
v___y_648_ = v___y_668_;
v___y_649_ = v___y_669_;
v___y_650_ = v___x_672_;
goto v___jp_636_;
}
}
v___jp_673_:
{
if (v___y_676_ == 0)
{
if (v___y_682_ == 0)
{
uint32_t v___x_686_; 
v___x_686_ = 10004;
v___y_658_ = v___y_676_;
v___y_659_ = v___y_678_;
v___y_660_ = v___y_677_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_683_;
v___y_663_ = v___y_682_;
v___y_664_ = v___y_685_;
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_679_;
v___y_668_ = v___y_680_;
v___y_669_ = v___y_681_;
v___y_670_ = v___x_686_;
goto v___jp_657_;
}
else
{
uint32_t v___x_687_; 
v___x_687_ = 8856;
v___y_658_ = v___y_676_;
v___y_659_ = v___y_678_;
v___y_660_ = v___y_677_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_683_;
v___y_663_ = v___y_682_;
v___y_664_ = v___y_685_;
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_679_;
v___y_668_ = v___y_680_;
v___y_669_ = v___y_681_;
v___y_670_ = v___x_687_;
goto v___jp_657_;
}
}
else
{
uint32_t v___x_688_; 
v___x_688_ = l_Lake_LogLevel_icon(v___y_677_);
v___y_658_ = v___y_676_;
v___y_659_ = v___y_678_;
v___y_660_ = v___y_677_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_683_;
v___y_663_ = v___y_682_;
v___y_664_ = v___y_685_;
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_679_;
v___y_668_ = v___y_680_;
v___y_669_ = v___y_681_;
v___y_670_ = v___x_688_;
goto v___jp_657_;
}
}
v___jp_689_:
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__8));
v___y_674_ = v___y_690_;
v___y_675_ = v___y_691_;
v___y_676_ = v___y_692_;
v___y_677_ = v___y_694_;
v___y_678_ = v___y_693_;
v___y_679_ = v___y_695_;
v___y_680_ = v___y_696_;
v___y_681_ = v___y_697_;
v___y_682_ = v___y_698_;
v___y_683_ = v___y_700_;
v___y_684_ = v___y_699_;
v___y_685_ = v___x_701_;
goto v___jp_673_;
}
v___jp_702_:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lake_JobAction_verb(v___y_711_, v___y_706_);
v___y_674_ = v___y_703_;
v___y_675_ = v___y_704_;
v___y_676_ = v___y_705_;
v___y_677_ = v___y_708_;
v___y_678_ = v___y_707_;
v___y_679_ = v___y_709_;
v___y_680_ = v___y_710_;
v___y_681_ = v___y_711_;
v___y_682_ = v___y_712_;
v___y_683_ = v___y_714_;
v___y_684_ = v___y_713_;
v___y_685_ = v___x_715_;
goto v___jp_673_;
}
v___jp_716_:
{
if (v___y_719_ == 0)
{
if (v___y_727_ == 0)
{
if (v_showProgress_481_ == 0)
{
lean_dec(v___y_726_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_721_);
lean_dec_ref(v_caption_582_);
lean_dec(v_totalJobs_469_);
lean_dec(v_jobNo_468_);
v___y_465_ = v___y_718_;
goto v___jp_464_;
}
else
{
if (v_useAnsi_480_ == 0)
{
uint8_t v___x_728_; 
v___x_728_ = l_Lake_instOrdJobAction_ord(v_minAction_478_, v___y_722_);
if (v___x_728_ == 2)
{
lean_dec(v___y_726_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_721_);
lean_dec_ref(v_caption_582_);
lean_dec(v_totalJobs_469_);
lean_dec(v_jobNo_468_);
v___y_465_ = v___y_718_;
goto v___jp_464_;
}
else
{
v___y_703_ = v___y_717_;
v___y_704_ = v___y_718_;
v___y_705_ = v___y_719_;
v___y_706_ = v___y_722_;
v___y_707_ = v___y_721_;
v___y_708_ = v___y_720_;
v___y_709_ = v___y_723_;
v___y_710_ = v___y_724_;
v___y_711_ = v___y_725_;
v___y_712_ = v___y_727_;
v___y_713_ = v___y_726_;
v___y_714_ = v_showProgress_481_;
goto v___jp_702_;
}
}
else
{
lean_dec(v___y_726_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_721_);
lean_dec_ref(v_caption_582_);
lean_dec(v_totalJobs_469_);
lean_dec(v_jobNo_468_);
v___y_465_ = v___y_718_;
goto v___jp_464_;
}
}
}
else
{
v___y_690_ = v___y_717_;
v___y_691_ = v___y_718_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_721_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_723_;
v___y_696_ = v___y_724_;
v___y_697_ = v___y_725_;
v___y_698_ = v___y_727_;
v___y_699_ = v___y_726_;
v___y_700_ = v___y_727_;
goto v___jp_689_;
}
}
else
{
if (v___y_727_ == 0)
{
v___y_703_ = v___y_717_;
v___y_704_ = v___y_718_;
v___y_705_ = v___y_719_;
v___y_706_ = v___y_722_;
v___y_707_ = v___y_721_;
v___y_708_ = v___y_720_;
v___y_709_ = v___y_723_;
v___y_710_ = v___y_724_;
v___y_711_ = v___y_725_;
v___y_712_ = v___y_727_;
v___y_713_ = v___y_726_;
v___y_714_ = v___y_719_;
goto v___jp_702_;
}
else
{
v___y_690_ = v___y_717_;
v___y_691_ = v___y_718_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_721_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_723_;
v___y_696_ = v___y_724_;
v___y_697_ = v___y_725_;
v___y_698_ = v___y_727_;
v___y_699_ = v___y_726_;
v___y_700_ = v___y_719_;
goto v___jp_689_;
}
}
}
v___jp_729_:
{
if (v_optional_583_ == 0)
{
v___y_717_ = v___y_730_;
v___y_718_ = v___y_731_;
v___y_719_ = v___y_740_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_739_;
goto v___jp_716_;
}
else
{
if (v_showOptional_479_ == 0)
{
lean_dec(v___y_738_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_733_);
lean_dec_ref(v_caption_582_);
lean_dec(v_totalJobs_469_);
lean_dec(v_jobNo_468_);
v___y_465_ = v___y_731_;
goto v___jp_464_;
}
else
{
v___y_717_ = v___y_730_;
v___y_718_ = v___y_731_;
v___y_719_ = v___y_740_;
v___y_720_ = v___y_732_;
v___y_721_ = v___y_733_;
v___y_722_ = v___y_734_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_739_;
goto v___jp_716_;
}
}
}
v___jp_741_:
{
if (v___y_748_ == 0)
{
if (v___y_742_ == 0)
{
v___y_730_ = v___y_751_;
v___y_731_ = v___y_752_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_743_;
v___y_735_ = v___y_746_;
v___y_736_ = v___y_747_;
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_742_;
goto v___jp_729_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = l_Lake_instOrdLogLevel_ord(v_outLv_476_, v___y_745_);
if (v___x_753_ == 2)
{
v___y_730_ = v___y_751_;
v___y_731_ = v___y_752_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_743_;
v___y_735_ = v___y_746_;
v___y_736_ = v___y_747_;
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_748_;
goto v___jp_729_;
}
else
{
v___y_730_ = v___y_751_;
v___y_731_ = v___y_752_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_743_;
v___y_735_ = v___y_746_;
v___y_736_ = v___y_747_;
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_742_;
goto v___jp_729_;
}
}
}
else
{
if (v_optional_583_ == 0)
{
lean_object* v_jobNo_754_; lean_object* v_totalJobs_755_; uint8_t v_wantsRebuild_756_; lean_object* v_failures_757_; lean_object* v_resetCtrl_758_; lean_object* v_lastUpdate_759_; lean_object* v_spinnerIdx_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_jobNo_754_ = lean_ctor_get(v___y_752_, 0);
v_totalJobs_755_ = lean_ctor_get(v___y_752_, 1);
v_wantsRebuild_756_ = lean_ctor_get_uint8(v___y_752_, sizeof(void*)*6);
v_failures_757_ = lean_ctor_get(v___y_752_, 2);
v_resetCtrl_758_ = lean_ctor_get(v___y_752_, 3);
v_lastUpdate_759_ = lean_ctor_get(v___y_752_, 4);
v_spinnerIdx_760_ = lean_ctor_get(v___y_752_, 5);
v_isSharedCheck_768_ = !lean_is_exclusive(v___y_752_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v___y_752_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_spinnerIdx_760_);
lean_inc(v_lastUpdate_759_);
lean_inc(v_resetCtrl_758_);
lean_inc(v_failures_757_);
lean_inc(v_totalJobs_755_);
lean_inc(v_jobNo_754_);
lean_dec(v___y_752_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
lean_inc_ref(v_caption_582_);
v___x_764_ = lean_array_push(v_failures_757_, v_caption_582_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 2, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_jobNo_754_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_totalJobs_755_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_resetCtrl_758_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_lastUpdate_759_);
lean_ctor_set(v_reuseFailAlloc_767_, 5, v_spinnerIdx_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*6, v_wantsRebuild_756_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v___y_730_ = v___y_751_;
v___y_731_ = v___x_766_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_743_;
v___y_735_ = v___y_746_;
v___y_736_ = v___y_747_;
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_748_;
goto v___jp_729_;
}
}
}
else
{
v___y_730_ = v___y_751_;
v___y_731_ = v___y_752_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_744_;
v___y_734_ = v___y_743_;
v___y_735_ = v___y_746_;
v___y_736_ = v___y_747_;
v___y_737_ = v___y_748_;
v___y_738_ = v___y_750_;
v___y_739_ = v___y_749_;
v___y_740_ = v___y_748_;
goto v___jp_729_;
}
}
}
v___jp_769_:
{
if (v___y_774_ == 0)
{
v___y_742_ = v___y_770_;
v___y_743_ = v___y_773_;
v___y_744_ = v___y_772_;
v___y_745_ = v___y_771_;
v___y_746_ = v___y_775_;
v___y_747_ = v___y_776_;
v___y_748_ = v___y_777_;
v___y_749_ = v___y_779_;
v___y_750_ = v___y_778_;
v___y_751_ = v_a_449_;
v___y_752_ = v_a_450_;
goto v___jp_741_;
}
else
{
if (v_wantsRebuild_470_ == 0)
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_inc(v_spinnerIdx_474_);
lean_inc(v_lastUpdate_473_);
lean_inc_ref(v_resetCtrl_472_);
lean_inc_ref(v_failures_471_);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_787_ = lean_ctor_get(v_a_450_, 5);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_a_450_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_a_450_, 3);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_a_450_, 2);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_a_450_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_a_450_, 0);
lean_dec(v_unused_792_);
v___x_781_ = v_a_450_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_a_450_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
lean_inc(v_totalJobs_469_);
lean_inc(v_jobNo_468_);
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_jobNo_468_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_totalJobs_469_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v_failures_471_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v_resetCtrl_472_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v_lastUpdate_473_);
lean_ctor_set(v_reuseFailAlloc_785_, 5, v_spinnerIdx_474_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*6, v___y_774_);
v___y_742_ = v___y_770_;
v___y_743_ = v___y_773_;
v___y_744_ = v___y_772_;
v___y_745_ = v___y_771_;
v___y_746_ = v___y_775_;
v___y_747_ = v___y_776_;
v___y_748_ = v___y_777_;
v___y_749_ = v___y_779_;
v___y_750_ = v___y_778_;
v___y_751_ = v_a_449_;
v___y_752_ = v___x_784_;
goto v___jp_741_;
}
}
}
else
{
v___y_742_ = v___y_770_;
v___y_743_ = v___y_773_;
v___y_744_ = v___y_772_;
v___y_745_ = v___y_771_;
v___y_746_ = v___y_775_;
v___y_747_ = v___y_776_;
v___y_748_ = v___y_777_;
v___y_749_ = v___y_779_;
v___y_750_ = v___y_778_;
v___y_751_ = v_a_449_;
v___y_752_ = v_a_450_;
goto v___jp_741_;
}
}
}
v___jp_793_:
{
uint8_t v___x_804_; 
v___x_804_ = lean_strict_and(v___y_794_, v___y_803_);
if (v___y_795_ == 0)
{
v___y_770_ = v___y_794_;
v___y_771_ = v___y_798_;
v___y_772_ = v___y_797_;
v___y_773_ = v___y_796_;
v___y_774_ = v___y_799_;
v___y_775_ = v___y_800_;
v___y_776_ = v___y_801_;
v___y_777_ = v___x_804_;
v___y_778_ = v___y_802_;
v___y_779_ = v___y_795_;
goto v___jp_769_;
}
else
{
if (v___x_804_ == 0)
{
v___y_770_ = v___y_794_;
v___y_771_ = v___y_798_;
v___y_772_ = v___y_797_;
v___y_773_ = v___y_796_;
v___y_774_ = v___y_799_;
v___y_775_ = v___y_800_;
v___y_776_ = v___y_801_;
v___y_777_ = v___x_804_;
v___y_778_ = v___y_802_;
v___y_779_ = v___y_795_;
goto v___jp_769_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 0;
v___y_770_ = v___y_794_;
v___y_771_ = v___y_798_;
v___y_772_ = v___y_797_;
v___y_773_ = v___y_796_;
v___y_774_ = v___y_799_;
v___y_775_ = v___y_800_;
v___y_776_ = v___y_801_;
v___y_777_ = v___x_804_;
v___y_778_ = v___y_802_;
v___y_779_ = v___x_805_;
goto v___jp_769_;
}
}
}
v___jp_806_:
{
uint8_t v___x_816_; 
v___x_816_ = l_Lake_instOrdLogLevel_ord(v_failLv_477_, v___y_808_);
if (v___x_816_ == 2)
{
uint8_t v___x_817_; 
v___x_817_ = 0;
v___y_794_ = v___y_815_;
v___y_795_ = v___y_807_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_809_;
v___y_798_ = v___y_808_;
v___y_799_ = v___y_811_;
v___y_800_ = v___y_812_;
v___y_801_ = v___y_813_;
v___y_802_ = v___y_814_;
v___y_803_ = v___x_817_;
goto v___jp_793_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = 1;
v___y_794_ = v___y_815_;
v___y_795_ = v___y_807_;
v___y_796_ = v___y_810_;
v___y_797_ = v___y_809_;
v___y_798_ = v___y_808_;
v___y_799_ = v___y_811_;
v___y_800_ = v___y_812_;
v___y_801_ = v___y_813_;
v___y_802_ = v___y_814_;
v___y_803_ = v___x_818_;
goto v___jp_793_;
}
}
v___jp_819_:
{
lean_object* v_log_821_; uint8_t v_action_822_; uint8_t v_wantsRebuild_823_; uint8_t v_canceled_824_; lean_object* v_buildTime_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_log_821_ = lean_ctor_get(v___y_820_, 0);
lean_inc_ref(v_log_821_);
v_action_822_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*3);
v_wantsRebuild_823_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*3 + 1);
v_canceled_824_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*3 + 2);
v_buildTime_825_ = lean_ctor_get(v___y_820_, 2);
lean_inc(v_buildTime_825_);
lean_dec_ref(v___y_820_);
v___x_826_ = l_Lake_Log_maxLv(v_log_821_);
v___x_827_ = lean_array_get_size(v_log_821_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_nat_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = 1;
v___y_807_ = v_canceled_824_;
v___y_808_ = v___x_826_;
v___y_809_ = v_buildTime_825_;
v___y_810_ = v_action_822_;
v___y_811_ = v_wantsRebuild_823_;
v___y_812_ = v_log_821_;
v___y_813_ = v___x_827_;
v___y_814_ = v___x_828_;
v___y_815_ = v___x_830_;
goto v___jp_806_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = 0;
v___y_807_ = v_canceled_824_;
v___y_808_ = v___x_826_;
v___y_809_ = v_buildTime_825_;
v___y_810_ = v_action_822_;
v___y_811_ = v_wantsRebuild_823_;
v___y_812_ = v_log_821_;
v___y_813_ = v___x_827_;
v___y_814_ = v___x_828_;
v___y_815_ = v___x_831_;
goto v___jp_806_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_job_448_ = stack[0].m_obj;
lean_object* v_a_449_ = stack[1].m_obj;
lean_object* v_a_450_ = stack[2].m_obj;
lean_object* v_res_834_;
v_res_834_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_448_, v_a_449_, v_a_450_);
stack->m_obj
 = v_res_834_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_835_, v_a_836_, v_a_837_);
lean_dec_ref(v_a_836_);
return v_res_839_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_840_, uint8_t v___y_841_, uint8_t v_useAnsi_842_, lean_object* v_as_843_, size_t v_i_844_, size_t v_stop_845_, lean_object* v_b_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_840_, v___y_841_, v_useAnsi_842_, v_as_843_, v_i_844_, v_stop_845_, v_b_846_, v___y_848_);
return v___x_850_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_840_ = stack[0].m_obj;
uint8_t v___y_841_ = stack[1].m_num;
uint8_t v_useAnsi_842_ = stack[2].m_num;
lean_object* v_as_843_ = stack[3].m_obj;
size_t v_i_844_ = stack[4].m_num;
size_t v_stop_845_ = stack[5].m_num;
lean_object* v_b_846_ = stack[6].m_obj;
lean_object* v___y_847_ = stack[7].m_obj;
lean_object* v___y_848_ = stack[8].m_obj;
lean_object* v_res_851_;
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_840_, v___y_841_, v_useAnsi_842_, v_as_843_, v_i_844_, v_stop_845_, v_b_846_, v___y_847_, v___y_848_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_852_, lean_object* v___y_853_, lean_object* v_useAnsi_854_, lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
uint8_t v___y_15472__boxed_862_; uint8_t v_useAnsi_15473__boxed_863_; size_t v_i_boxed_864_; size_t v_stop_boxed_865_; lean_object* v_res_866_; 
v___y_15472__boxed_862_ = lean_unbox(v___y_853_);
v_useAnsi_15473__boxed_863_ = lean_unbox(v_useAnsi_854_);
v_i_boxed_864_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_865_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_852_, v___y_15472__boxed_862_, v_useAnsi_15473__boxed_863_, v_as_855_, v_i_boxed_864_, v_stop_boxed_865_, v_b_858_, v___y_859_, v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_as_855_);
return v_res_866_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_jobs_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_jobNo_876_; lean_object* v_totalJobs_877_; uint8_t v_wantsRebuild_878_; lean_object* v_failures_879_; lean_object* v_resetCtrl_880_; lean_object* v_lastUpdate_881_; lean_object* v_spinnerIdx_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_892_; 
v_jobs_872_ = lean_ctor_get(v_a_869_, 0);
v___x_873_ = lean_st_ref_take(v_jobs_872_);
v___x_874_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_875_ = lean_st_ref_put(v_jobs_872_, v___x_874_);
v_jobNo_876_ = lean_ctor_get(v_a_870_, 0);
v_totalJobs_877_ = lean_ctor_get(v_a_870_, 1);
v_wantsRebuild_878_ = lean_ctor_get_uint8(v_a_870_, sizeof(void*)*6);
v_failures_879_ = lean_ctor_get(v_a_870_, 2);
v_resetCtrl_880_ = lean_ctor_get(v_a_870_, 3);
v_lastUpdate_881_ = lean_ctor_get(v_a_870_, 4);
v_spinnerIdx_882_ = lean_ctor_get(v_a_870_, 5);
v_isSharedCheck_892_ = !lean_is_exclusive(v_a_870_);
if (v_isSharedCheck_892_ == 0)
{
v___x_884_ = v_a_870_;
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_spinnerIdx_882_);
lean_inc(v_lastUpdate_881_);
lean_inc(v_resetCtrl_880_);
lean_inc(v_failures_879_);
lean_inc(v_totalJobs_877_);
lean_inc(v_jobNo_876_);
lean_dec(v_a_870_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = lean_array_get_size(v___x_873_);
v___x_887_ = lean_nat_add(v_totalJobs_877_, v___x_886_);
lean_dec(v_totalJobs_877_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_887_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_jobNo_876_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_failures_879_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_resetCtrl_880_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v_lastUpdate_881_);
lean_ctor_set(v_reuseFailAlloc_891_, 5, v_spinnerIdx_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*6, v_wantsRebuild_878_);
v___x_889_ = v_reuseFailAlloc_891_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_873_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_869_ = stack[0].m_obj;
lean_object* v_a_870_ = stack[1].m_obj;
lean_object* v_res_893_;
v_res_893_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_869_, v_a_870_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_894_, v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_897_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object* v_as_898_, size_t v_i_899_, size_t v_stop_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_fst_906_; lean_object* v_snd_907_; uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_eq(v_i_899_, v_stop_900_);
if (v___x_911_ == 0)
{
lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v___x_914_; lean_object* v_task_915_; uint8_t v___x_916_; 
v_fst_912_ = lean_ctor_get(v_b_901_, 0);
v_snd_913_ = lean_ctor_get(v_b_901_, 1);
v___x_914_ = lean_array_uget_borrowed(v_as_898_, v_i_899_);
v_task_915_ = lean_ctor_get(v___x_914_, 0);
v___x_916_ = lean_io_get_task_state(v_task_915_);
switch(v___x_916_)
{
case 0:
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
lean_inc(v_snd_913_);
lean_inc(v_fst_912_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_b_901_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; lean_object* v_unused_926_; 
v_unused_925_ = lean_ctor_get(v_b_901_, 1);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_b_901_, 0);
lean_dec(v_unused_926_);
v___x_918_ = v_b_901_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_dec(v_b_901_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_inc(v___x_914_);
v___x_920_ = lean_array_push(v_snd_913_, v___x_914_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_fst_912_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
v_fst_906_ = v___x_922_;
v_snd_907_ = v___y_903_;
goto v___jp_905_;
}
}
}
case 1:
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_935_; 
lean_inc(v_snd_913_);
lean_inc(v_fst_912_);
v_isSharedCheck_935_ = !lean_is_exclusive(v_b_901_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; lean_object* v_unused_937_; 
v_unused_936_ = lean_ctor_get(v_b_901_, 1);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_b_901_, 0);
lean_dec(v_unused_937_);
v___x_928_ = v_b_901_;
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
else
{
lean_dec(v_b_901_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
lean_inc_n(v___x_914_, 2);
v___x_930_ = lean_array_push(v_fst_912_, v___x_914_);
v___x_931_ = lean_array_push(v_snd_913_, v___x_914_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_931_);
lean_ctor_set(v___x_928_, 0, v___x_930_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
v_fst_906_ = v___x_933_;
v_snd_907_ = v___y_903_;
goto v___jp_905_;
}
}
}
default: 
{
lean_object* v___x_938_; lean_object* v_snd_939_; lean_object* v_jobNo_940_; lean_object* v_totalJobs_941_; uint8_t v_wantsRebuild_942_; lean_object* v_failures_943_; lean_object* v_resetCtrl_944_; lean_object* v_lastUpdate_945_; lean_object* v_spinnerIdx_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
lean_inc(v___x_914_);
v___x_938_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_914_, v___y_902_, v___y_903_);
v_snd_939_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_snd_939_);
lean_dec_ref(v___x_938_);
v_jobNo_940_ = lean_ctor_get(v_snd_939_, 0);
v_totalJobs_941_ = lean_ctor_get(v_snd_939_, 1);
v_wantsRebuild_942_ = lean_ctor_get_uint8(v_snd_939_, sizeof(void*)*6);
v_failures_943_ = lean_ctor_get(v_snd_939_, 2);
v_resetCtrl_944_ = lean_ctor_get(v_snd_939_, 3);
v_lastUpdate_945_ = lean_ctor_get(v_snd_939_, 4);
v_spinnerIdx_946_ = lean_ctor_get(v_snd_939_, 5);
v_isSharedCheck_955_ = !lean_is_exclusive(v_snd_939_);
if (v_isSharedCheck_955_ == 0)
{
v___x_948_ = v_snd_939_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_spinnerIdx_946_);
lean_inc(v_lastUpdate_945_);
lean_inc(v_resetCtrl_944_);
lean_inc(v_failures_943_);
lean_inc(v_totalJobs_941_);
lean_inc(v_jobNo_940_);
lean_dec(v_snd_939_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_add(v_jobNo_940_, v___x_950_);
lean_dec(v_jobNo_940_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_totalJobs_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_failures_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_resetCtrl_944_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_lastUpdate_945_);
lean_ctor_set(v_reuseFailAlloc_954_, 5, v_spinnerIdx_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*6, v_wantsRebuild_942_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
v_fst_906_ = v_b_901_;
v_snd_907_ = v___x_953_;
goto v___jp_905_;
}
}
}
}
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_b_901_);
lean_ctor_set(v___x_956_, 1, v___y_903_);
return v___x_956_;
}
v___jp_905_:
{
size_t v___x_908_; size_t v___x_909_; 
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_add(v_i_899_, v___x_908_);
v_i_899_ = v___x_909_;
v_b_901_ = v_fst_906_;
v___y_903_ = v_snd_907_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_898_ = stack[0].m_obj;
size_t v_i_899_ = stack[1].m_num;
size_t v_stop_900_ = stack[2].m_num;
lean_object* v_b_901_ = stack[3].m_obj;
lean_object* v___y_902_ = stack[4].m_obj;
lean_object* v___y_903_ = stack[5].m_obj;
lean_object* v_res_957_;
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_898_, v_i_899_, v_stop_900_, v_b_901_, v___y_902_, v___y_903_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_stop_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
size_t v_i_boxed_965_; size_t v_stop_boxed_966_; lean_object* v_res_967_; 
v_i_boxed_965_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_stop_boxed_966_ = lean_unbox_usize(v_stop_960_);
lean_dec(v_stop_960_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_958_, v_i_boxed_965_, v_stop_boxed_966_, v_b_961_, v___y_962_, v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_as_958_);
return v_res_967_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object* v_new_970_, lean_object* v_unfinished_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___y_977_; lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___y_990_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_993_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_994_ = lean_array_get_size(v_unfinished_971_);
v___x_995_ = lean_nat_dec_lt(v___x_975_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_inc_ref(v_a_973_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_993_);
lean_ctor_set(v___x_996_, 1, v_a_973_);
v___y_977_ = v___x_996_;
v_fst_978_ = v___x_993_;
v_snd_979_ = v_a_973_;
goto v___jp_976_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = lean_nat_dec_le(v___x_994_, v___x_994_);
if (v___x_997_ == 0)
{
if (v___x_995_ == 0)
{
lean_object* v___x_998_; 
lean_inc_ref(v_a_973_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_993_);
lean_ctor_set(v___x_998_, 1, v_a_973_);
v___y_977_ = v___x_998_;
v_fst_978_ = v___x_993_;
v_snd_979_ = v_a_973_;
goto v___jp_976_;
}
else
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = lean_usize_of_nat(v___x_994_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_971_, v___x_999_, v___x_1000_, v___x_993_, v_a_972_, v_a_973_);
v___y_990_ = v___x_1001_;
goto v___jp_989_;
}
}
else
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = lean_usize_of_nat(v___x_994_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_971_, v___x_1002_, v___x_1003_, v___x_993_, v_a_972_, v_a_973_);
v___y_990_ = v___x_1004_;
goto v___jp_989_;
}
}
v___jp_976_:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_array_get_size(v_new_970_);
v___x_981_ = lean_nat_dec_lt(v___x_975_, v___x_980_);
if (v___x_981_ == 0)
{
lean_dec_ref(v_snd_979_);
lean_dec_ref(v_fst_978_);
return v___y_977_;
}
else
{
uint8_t v___x_982_; 
v___x_982_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_982_ == 0)
{
if (v___x_981_ == 0)
{
lean_dec_ref(v_snd_979_);
lean_dec_ref(v_fst_978_);
return v___y_977_;
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v___y_977_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_980_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_970_, v___x_983_, v___x_984_, v_fst_978_, v_a_972_, v_snd_979_);
return v___x_985_;
}
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v___y_977_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_980_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_970_, v___x_986_, v___x_987_, v_fst_978_, v_a_972_, v_snd_979_);
return v___x_988_;
}
}
}
v___jp_989_:
{
lean_object* v_fst_991_; lean_object* v_snd_992_; 
v_fst_991_ = lean_ctor_get(v___y_990_, 0);
lean_inc(v_fst_991_);
v_snd_992_ = lean_ctor_get(v___y_990_, 1);
lean_inc(v_snd_992_);
v___y_977_ = v___y_990_;
v_fst_978_ = v_fst_991_;
v_snd_979_ = v_snd_992_;
goto v___jp_976_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs_0interp(lean_interpreter_value* stack)
{
lean_object* v_new_970_ = stack[0].m_obj;
lean_object* v_unfinished_971_ = stack[1].m_obj;
lean_object* v_a_972_ = stack[2].m_obj;
lean_object* v_a_973_ = stack[3].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_970_, v_unfinished_971_, v_a_972_, v_a_973_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_1006_, lean_object* v_unfinished_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1006_, v_unfinished_1007_, v_a_1008_, v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec_ref(v_unfinished_1007_);
lean_dec_ref(v_new_1006_);
return v_res_1011_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___y_1016_; lean_object* v___x_1034_; lean_object* v_lastUpdate_1035_; lean_object* v_updateFrequency_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1034_ = lean_io_mono_ms_now();
v_lastUpdate_1035_ = lean_ctor_get(v_a_1013_, 4);
v_updateFrequency_1036_ = lean_ctor_get(v_a_1012_, 2);
v___x_1037_ = lean_nat_sub(v___x_1034_, v_lastUpdate_1035_);
lean_dec(v___x_1034_);
v___x_1038_ = lean_nat_sub(v_updateFrequency_1036_, v___x_1037_);
lean_dec(v___x_1037_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_nat_dec_lt(v___x_1039_, v___x_1038_);
if (v___x_1040_ == 0)
{
lean_dec(v___x_1038_);
v___y_1016_ = v_a_1013_;
goto v___jp_1015_;
}
else
{
uint32_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_uint32_of_nat(v___x_1038_);
lean_dec(v___x_1038_);
v___x_1042_ = l_IO_sleep(v___x_1041_);
v___y_1016_ = v_a_1013_;
goto v___jp_1015_;
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v_jobNo_1018_; lean_object* v_totalJobs_1019_; uint8_t v_wantsRebuild_1020_; lean_object* v_failures_1021_; lean_object* v_resetCtrl_1022_; lean_object* v_spinnerIdx_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1032_; 
v___x_1017_ = lean_io_mono_ms_now();
v_jobNo_1018_ = lean_ctor_get(v___y_1016_, 0);
v_totalJobs_1019_ = lean_ctor_get(v___y_1016_, 1);
v_wantsRebuild_1020_ = lean_ctor_get_uint8(v___y_1016_, sizeof(void*)*6);
v_failures_1021_ = lean_ctor_get(v___y_1016_, 2);
v_resetCtrl_1022_ = lean_ctor_get(v___y_1016_, 3);
v_spinnerIdx_1023_ = lean_ctor_get(v___y_1016_, 5);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___y_1016_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___y_1016_, 4);
lean_dec(v_unused_1033_);
v___x_1025_ = v___y_1016_;
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_spinnerIdx_1023_);
lean_inc(v_resetCtrl_1022_);
lean_inc(v_failures_1021_);
lean_inc(v_totalJobs_1019_);
lean_inc(v_jobNo_1018_);
lean_dec(v___y_1016_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v___x_1017_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_jobNo_1018_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_totalJobs_1019_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_failures_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_resetCtrl_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1031_, 5, v_spinnerIdx_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*6, v_wantsRebuild_1020_);
v___x_1029_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1027_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_sleep_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1012_ = stack[0].m_obj;
lean_object* v_a_1013_ = stack[1].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1012_, v_a_1013_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1044_, v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1047_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_1048_, lean_object* v_unfinished_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; lean_object* v_fst_1054_; lean_object* v_snd_1055_; lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___y_1059_; lean_object* v___y_1060_; uint8_t v_failFast_1086_; 
v___x_1053_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1048_, v_unfinished_1049_, v_a_1050_, v_a_1051_);
lean_dec_ref(v_unfinished_1049_);
lean_dec_ref(v_new_1048_);
v_fst_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_fst_1054_);
v_snd_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_snd_1055_);
lean_dec_ref(v___x_1053_);
v_fst_1056_ = lean_ctor_get(v_fst_1054_, 0);
lean_inc(v_fst_1056_);
v_snd_1057_ = lean_ctor_get(v_fst_1054_, 1);
lean_inc(v_snd_1057_);
lean_dec(v_fst_1054_);
v_failFast_1086_ = lean_ctor_get_uint8(v_a_1050_, sizeof(void*)*4 + 7);
if (v_failFast_1086_ == 0)
{
v___y_1059_ = v_a_1050_;
v___y_1060_ = v_snd_1055_;
goto v___jp_1058_;
}
else
{
lean_object* v_cancelTk_x3f_1087_; 
v_cancelTk_x3f_1087_ = lean_ctor_get(v_a_1050_, 3);
if (lean_obj_tag(v_cancelTk_x3f_1087_) == 1)
{
lean_object* v_val_1088_; lean_object* v_failures_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_val_1088_ = lean_ctor_get(v_cancelTk_x3f_1087_, 0);
v_failures_1089_ = lean_ctor_get(v_snd_1055_, 2);
v___x_1090_ = lean_array_get_size(v_failures_1089_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_nat_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = l_IO_CancelToken_set(v_val_1088_);
v___y_1059_ = v_a_1050_;
v___y_1060_ = v_snd_1055_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v_a_1050_;
v___y_1060_ = v_snd_1055_;
goto v___jp_1058_;
}
}
else
{
v___y_1059_ = v_a_1050_;
v___y_1060_ = v_snd_1055_;
goto v___jp_1058_;
}
}
v___jp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_array_get_size(v_snd_1057_);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_fst_1056_);
v___x_1064_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1059_, v___y_1060_);
v_fst_1065_ = lean_ctor_get(v___x_1064_, 0);
v_snd_1066_ = lean_ctor_get(v___x_1064_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1068_ = v___x_1064_;
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v___x_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_array_get_size(v_fst_1065_);
v___x_1071_ = lean_nat_dec_lt(v___x_1061_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
lean_dec(v_fst_1065_);
lean_dec(v_snd_1057_);
v___x_1072_ = lean_box(0);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_snd_1066_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_del_object(v___x_1068_);
v_new_1048_ = v_fst_1065_;
v_unfinished_1049_ = v_snd_1057_;
v_a_1050_ = v___y_1059_;
v_a_1051_ = v_snd_1066_;
goto _start;
}
}
}
else
{
lean_object* v___x_1078_; lean_object* v_snd_1079_; lean_object* v___x_1080_; lean_object* v_snd_1081_; lean_object* v___x_1082_; lean_object* v_fst_1083_; lean_object* v_snd_1084_; 
v___x_1078_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1056_, v_snd_1057_, v___y_1059_, v___y_1060_);
lean_dec(v_fst_1056_);
v_snd_1079_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_snd_1079_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v___y_1059_, v_snd_1079_);
v_snd_1081_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_snd_1081_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1059_, v_snd_1081_);
v_fst_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_fst_1083_);
v_snd_1084_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_snd_1084_);
lean_dec_ref(v___x_1082_);
v_new_1048_ = v_fst_1083_;
v_unfinished_1049_ = v_snd_1057_;
v_a_1050_ = v___y_1059_;
v_a_1051_ = v_snd_1084_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_new_1048_ = stack[0].m_obj;
lean_object* v_unfinished_1049_ = stack[1].m_obj;
lean_object* v_a_1050_ = stack[2].m_obj;
lean_object* v_a_1051_ = stack[3].m_obj;
lean_object* v_res_1094_;
v_res_1094_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1048_, v_unfinished_1049_, v_a_1050_, v_a_1051_);
stack->m_obj
 = v_res_1094_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1095_, lean_object* v_unfinished_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1095_, v_unfinished_1096_, v_a_1097_, v_a_1098_);
lean_dec_ref(v_a_1097_);
return v_res_1100_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1176_; 
v___x_1105_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1102_, v_a_1103_);
v_fst_1106_ = lean_ctor_get(v___x_1105_, 0);
v_snd_1107_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1176_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_inc(v_fst_1106_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1176_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1174_; 
v___x_1111_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1106_, v_init_1101_, v_a_1102_, v_snd_1107_);
v_snd_1112_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v___x_1111_, 0);
lean_dec(v_unused_1175_);
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1174_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1174_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_jobNo_1116_; lean_object* v_totalJobs_1117_; uint8_t v_wantsRebuild_1118_; lean_object* v_failures_1119_; lean_object* v_resetCtrl_1120_; lean_object* v_lastUpdate_1121_; lean_object* v_spinnerIdx_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1173_; 
v_jobNo_1116_ = lean_ctor_get(v_snd_1112_, 0);
v_totalJobs_1117_ = lean_ctor_get(v_snd_1112_, 1);
v_wantsRebuild_1118_ = lean_ctor_get_uint8(v_snd_1112_, sizeof(void*)*6);
v_failures_1119_ = lean_ctor_get(v_snd_1112_, 2);
v_resetCtrl_1120_ = lean_ctor_get(v_snd_1112_, 3);
v_lastUpdate_1121_ = lean_ctor_get(v_snd_1112_, 4);
v_spinnerIdx_1122_ = lean_ctor_get(v_snd_1112_, 5);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_snd_1112_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1124_ = v_snd_1112_;
v_isShared_1125_ = v_isSharedCheck_1173_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_spinnerIdx_1122_);
lean_inc(v_lastUpdate_1121_);
lean_inc(v_resetCtrl_1120_);
lean_inc(v_failures_1119_);
lean_inc(v_totalJobs_1117_);
lean_inc(v_jobNo_1116_);
lean_dec(v_snd_1112_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1173_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 3, v___x_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_jobNo_1116_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_totalJobs_1117_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_failures_1119_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_lastUpdate_1121_);
lean_ctor_set(v_reuseFailAlloc_1172_, 5, v_spinnerIdx_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*6, v_wantsRebuild_1118_);
v___x_1128_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v_val_1130_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_string_utf8_byte_size(v_resetCtrl_1120_);
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v_out_1137_; lean_object* v_flush_1138_; lean_object* v_putStr_1139_; lean_object* v___x_1144_; 
lean_del_object(v___x_1109_);
v_out_1137_ = lean_ctor_get(v_a_1102_, 1);
v_flush_1138_ = lean_ctor_get(v_out_1137_, 0);
v_putStr_1139_ = lean_ctor_get(v_out_1137_, 4);
lean_inc_ref(v_putStr_1139_);
lean_inc_ref(v_resetCtrl_1120_);
v___x_1144_ = lean_apply_2(v_putStr_1139_, v_resetCtrl_1120_, lean_box(0));
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec_ref_known(v___x_1144_, 1);
lean_dec_ref(v_resetCtrl_1120_);
goto v___jp_1140_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1167_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1167_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1167_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1149_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1150_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1151_ = lean_unsigned_to_nat(82u);
v___x_1152_ = lean_unsigned_to_nat(4u);
v___x_1153_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1154_ = lean_io_error_to_string(v_a_1145_);
v___x_1155_ = lean_string_append(v___x_1153_, v___x_1154_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1157_ = lean_string_append(v___x_1155_, v___x_1156_);
v___x_1158_ = l_String_quote(v_resetCtrl_1120_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 3);
lean_ctor_set(v___x_1147_, 0, v___x_1158_);
v___x_1160_ = v___x_1147_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1161_ = l_Std_Format_defWidth;
v___x_1162_ = l_Std_Format_pretty(v___x_1160_, v___x_1161_, v___x_1135_, v___x_1135_);
v___x_1163_ = lean_string_append(v___x_1157_, v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = l_mkPanicMessageWithDecl(v___x_1149_, v___x_1150_, v___x_1151_, v___x_1152_, v___x_1163_);
lean_dec_ref(v___x_1163_);
v___x_1165_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1164_);
goto v___jp_1140_;
}
}
}
v___jp_1140_:
{
lean_object* v___x_1141_; 
lean_inc_ref(v_flush_1138_);
v___x_1141_ = lean_apply_1(v_flush_1138_, lean_box(0));
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v_val_1130_ = v_a_1142_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1143_; 
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_box(0);
v_val_1130_ = v___x_1143_;
goto v___jp_1129_;
}
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_dec_ref(v_resetCtrl_1120_);
lean_del_object(v___x_1114_);
v___x_1168_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1128_);
lean_ctor_set(v___x_1109_, 0, v___x_1168_);
v___x_1170_ = v___x_1109_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___x_1128_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
v___jp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1128_);
lean_ctor_set(v___x_1114_, 0, v_val_1130_);
v___x_1132_ = v___x_1114_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_val_1130_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1128_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Monitor_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1101_ = stack[0].m_obj;
lean_object* v_a_1102_ = stack[1].m_obj;
lean_object* v_a_1103_ = stack[2].m_obj;
lean_object* v_res_1177_;
v_res_1177_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1101_, v_a_1102_, v_a_1103_);
stack->m_obj
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1178_, v_a_1179_, v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1182_;
}
}
uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1183_){
_start:
{
lean_object* v_failures_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_failures_1184_ = lean_ctor_get(v_self_1183_, 0);
v___x_1185_ = lean_array_get_size(v_failures_1184_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_nat_dec_eq(v___x_1185_, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1183_ = stack[0].m_obj;
uint8_t v_res_1188_;
v_res_1188_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1183_);
stack->m_num = v_res_1188_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1189_);
lean_dec_ref(v_self_1189_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1192_, lean_object* v_jobs_1193_, lean_object* v_cancelTk_x3f_1194_){
_start:
{
lean_object* v_toLogConfig_1196_; uint8_t v_failFast_1197_; uint8_t v_verbosity_1198_; uint8_t v_failLv_1199_; uint8_t v_outLv_1200_; uint8_t v_ansiMode_1201_; lean_object* v_out_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; uint8_t v___y_1211_; uint8_t v___y_1212_; uint8_t v___y_1216_; 
v_toLogConfig_1196_ = lean_ctor_get(v_cfg_1192_, 0);
v_failFast_1197_ = lean_ctor_get_uint8(v_cfg_1192_, sizeof(void*)*5 + 3);
v_verbosity_1198_ = lean_ctor_get_uint8(v_cfg_1192_, sizeof(void*)*5 + 4);
v_failLv_1199_ = lean_ctor_get_uint8(v_toLogConfig_1196_, sizeof(void*)*1);
v_outLv_1200_ = lean_ctor_get_uint8(v_toLogConfig_1196_, sizeof(void*)*1 + 1);
v_ansiMode_1201_ = lean_ctor_get_uint8(v_toLogConfig_1196_, sizeof(void*)*1 + 2);
v_out_1202_ = lean_ctor_get(v_toLogConfig_1196_, 0);
v___x_1203_ = l_Lake_OutStream_get(v_out_1202_);
lean_inc_ref(v___x_1203_);
v___x_1204_ = l_Lake_AnsiMode_isEnabled(v___x_1203_, v_ansiMode_1201_);
v___x_1205_ = l_Lake_BuildConfig_showProgress(v_cfg_1192_);
v___x_1206_ = lean_box(v_verbosity_1198_);
v___x_1207_ = lean_obj_tag_nat(v___x_1206_);
lean_dec(v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(2u);
v___x_1209_ = lean_nat_dec_eq(v___x_1207_, v___x_1208_);
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
v___x_1214_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_1214_, 0, v_jobs_1193_);
lean_ctor_set(v___x_1214_, 1, v___x_1203_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
lean_ctor_set(v___x_1214_, 3, v_cancelTk_x3f_1194_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4, v_outLv_1200_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 1, v_failLv_1199_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 2, v___y_1211_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 3, v___x_1209_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 4, v___x_1204_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 5, v___x_1205_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 6, v___y_1212_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*4 + 7, v_failFast_1197_);
return v___x_1214_;
}
v___jp_1215_:
{
if (v___x_1209_ == 0)
{
if (v___x_1204_ == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = 1;
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
else
{
v___y_1211_ = v___y_1216_;
v___y_1212_ = v___x_1209_;
goto v___jp_1210_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_mkMonitorContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1192_ = stack[0].m_obj;
lean_object* v_jobs_1193_ = stack[1].m_obj;
lean_object* v_cancelTk_x3f_1194_ = stack[2].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1192_, v_jobs_1193_, v_cancelTk_x3f_1194_);
stack->m_obj
 = v_res_1220_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1221_, lean_object* v_jobs_1222_, lean_object* v_cancelTk_x3f_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1221_, v_jobs_1222_, v_cancelTk_x3f_1223_);
lean_dec_ref(v_cfg_1221_);
return v_res_1225_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1226_, lean_object* v_initJobs_1227_, lean_object* v_initFailures_1228_, lean_object* v_resetCtrl_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_snd_1236_; lean_object* v_totalJobs_1237_; uint8_t v_wantsRebuild_1238_; lean_object* v_failures_1239_; lean_object* v___x_1240_; 
v___x_1231_ = lean_io_mono_ms_now();
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = 0;
v___x_1234_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
lean_ctor_set(v___x_1234_, 2, v_initFailures_1228_);
lean_ctor_set(v___x_1234_, 3, v_resetCtrl_1229_);
lean_ctor_set(v___x_1234_, 4, v___x_1231_);
lean_ctor_set(v___x_1234_, 5, v___x_1232_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*6, v___x_1233_);
v___x_1235_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1227_, v_ctx_1226_, v___x_1234_);
v_snd_1236_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_snd_1236_);
lean_dec_ref(v___x_1235_);
v_totalJobs_1237_ = lean_ctor_get(v_snd_1236_, 1);
lean_inc(v_totalJobs_1237_);
v_wantsRebuild_1238_ = lean_ctor_get_uint8(v_snd_1236_, sizeof(void*)*6);
v_failures_1239_ = lean_ctor_get(v_snd_1236_, 2);
lean_inc_ref(v_failures_1239_);
lean_dec(v_snd_1236_);
v___x_1240_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1240_, 0, v_failures_1239_);
lean_ctor_set(v___x_1240_, 1, v_totalJobs_1237_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*2, v_wantsRebuild_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_monitorJobs_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1226_ = stack[0].m_obj;
lean_object* v_initJobs_1227_ = stack[1].m_obj;
lean_object* v_initFailures_1228_ = stack[2].m_obj;
lean_object* v_resetCtrl_1229_ = stack[3].m_obj;
lean_object* v_res_1241_;
v_res_1241_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1226_, v_initJobs_1227_, v_initFailures_1228_, v_resetCtrl_1229_);
stack->m_obj
 = v_res_1241_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1242_, lean_object* v_initJobs_1243_, lean_object* v_initFailures_1244_, lean_object* v_resetCtrl_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1242_, v_initJobs_1243_, v_initFailures_1244_, v_resetCtrl_1245_);
lean_dec_ref(v_ctx_1242_);
return v_res_1247_;
}
}
lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1248_, lean_object* v_jobs_1249_, lean_object* v_out_1250_, uint8_t v_failLv_1251_, uint8_t v_outLv_1252_, uint8_t v_minAction_1253_, uint8_t v_showOptional_1254_, uint8_t v_useAnsi_1255_, uint8_t v_showProgress_1256_, uint8_t v_showTime_1257_, lean_object* v_resetCtrl_1258_, lean_object* v_initFailures_1259_, lean_object* v_updateFrequency_1260_){
_start:
{
uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v_ctx_1264_; lean_object* v___x_1265_; 
v___x_1262_ = 0;
v___x_1263_ = lean_box(0);
v_ctx_1264_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_ctx_1264_, 0, v_jobs_1249_);
lean_ctor_set(v_ctx_1264_, 1, v_out_1250_);
lean_ctor_set(v_ctx_1264_, 2, v_updateFrequency_1260_);
lean_ctor_set(v_ctx_1264_, 3, v___x_1263_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4, v_outLv_1252_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 1, v_failLv_1251_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 2, v_minAction_1253_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 3, v_showOptional_1254_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 4, v_useAnsi_1255_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 5, v_showProgress_1256_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 6, v_showTime_1257_);
lean_ctor_set_uint8(v_ctx_1264_, sizeof(void*)*4 + 7, v___x_1262_);
v___x_1265_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1264_, v_initJobs_1248_, v_initFailures_1259_, v_resetCtrl_1258_);
lean_dec_ref_known(v_ctx_1264_, 4);
return v___x_1265_;
}
}
LEAN_EXPORT void l_Lake_monitorJobs_0interp(lean_interpreter_value* stack)
{
lean_object* v_initJobs_1248_ = stack[0].m_obj;
lean_object* v_jobs_1249_ = stack[1].m_obj;
lean_object* v_out_1250_ = stack[2].m_obj;
uint8_t v_failLv_1251_ = stack[3].m_num;
uint8_t v_outLv_1252_ = stack[4].m_num;
uint8_t v_minAction_1253_ = stack[5].m_num;
uint8_t v_showOptional_1254_ = stack[6].m_num;
uint8_t v_useAnsi_1255_ = stack[7].m_num;
uint8_t v_showProgress_1256_ = stack[8].m_num;
uint8_t v_showTime_1257_ = stack[9].m_num;
lean_object* v_resetCtrl_1258_ = stack[10].m_obj;
lean_object* v_initFailures_1259_ = stack[11].m_obj;
lean_object* v_updateFrequency_1260_ = stack[12].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l_Lake_monitorJobs(v_initJobs_1248_, v_jobs_1249_, v_out_1250_, v_failLv_1251_, v_outLv_1252_, v_minAction_1253_, v_showOptional_1254_, v_useAnsi_1255_, v_showProgress_1256_, v_showTime_1257_, v_resetCtrl_1258_, v_initFailures_1259_, v_updateFrequency_1260_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1267_, lean_object* v_jobs_1268_, lean_object* v_out_1269_, lean_object* v_failLv_1270_, lean_object* v_outLv_1271_, lean_object* v_minAction_1272_, lean_object* v_showOptional_1273_, lean_object* v_useAnsi_1274_, lean_object* v_showProgress_1275_, lean_object* v_showTime_1276_, lean_object* v_resetCtrl_1277_, lean_object* v_initFailures_1278_, lean_object* v_updateFrequency_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v_failLv_boxed_1281_; uint8_t v_outLv_boxed_1282_; uint8_t v_minAction_boxed_1283_; uint8_t v_showOptional_boxed_1284_; uint8_t v_useAnsi_boxed_1285_; uint8_t v_showProgress_boxed_1286_; uint8_t v_showTime_boxed_1287_; lean_object* v_res_1288_; 
v_failLv_boxed_1281_ = lean_unbox(v_failLv_1270_);
v_outLv_boxed_1282_ = lean_unbox(v_outLv_1271_);
v_minAction_boxed_1283_ = lean_unbox(v_minAction_1272_);
v_showOptional_boxed_1284_ = lean_unbox(v_showOptional_1273_);
v_useAnsi_boxed_1285_ = lean_unbox(v_useAnsi_1274_);
v_showProgress_boxed_1286_ = lean_unbox(v_showProgress_1275_);
v_showTime_boxed_1287_ = lean_unbox(v_showTime_1276_);
v_res_1288_ = l_Lake_monitorJobs(v_initJobs_1267_, v_jobs_1268_, v_out_1269_, v_failLv_boxed_1281_, v_outLv_boxed_1282_, v_minAction_boxed_1283_, v_showOptional_boxed_1284_, v_useAnsi_boxed_1285_, v_showProgress_boxed_1286_, v_showTime_boxed_1287_, v_resetCtrl_1277_, v_initFailures_1278_, v_updateFrequency_1279_);
return v_res_1288_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1289_; 
v___x_1289_ = 3;
return v___x_1289_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(lean_object* v_logger_1290_, lean_object* v_x_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_apply_2(v_logger_1290_, v___y_1292_, lean_box(0));
return v___x_1294_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_logger_1290_ = stack[0].m_obj;
lean_object* v_x_1291_ = stack[1].m_obj;
lean_object* v___y_1292_ = stack[2].m_obj;
lean_object* v_res_1295_;
v_res_1295_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(v_logger_1290_, v_x_1291_, v___y_1292_);
stack->m_obj
 = v_res_1295_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed(lean_object* v_logger_1296_, lean_object* v_x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(v_logger_1296_, v_x_1297_, v___y_1298_);
return v_res_1300_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1303_ = l_String_quote(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1);
v___x_1305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = l_Std_Format_defWidth;
v___x_1308_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2);
v___x_1309_ = l_Std_Format_pretty(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1306_);
return v___x_1309_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1317_ = l_String_quote(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8);
v___x_1319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = l_Std_Format_defWidth;
v___x_1322_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9);
v___x_1323_ = l_Std_Format_pretty(v___x_1322_, v___x_1321_, v___x_1320_, v___x_1320_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1326_ = l_String_quote(v___x_1325_);
return v___x_1326_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12);
v___x_1328_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = l_Std_Format_defWidth;
v___x_1331_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13);
v___x_1332_ = l_Std_Format_pretty(v___x_1331_, v___x_1330_, v___x_1329_, v___x_1329_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1336_ = l_String_quote(v___x_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17);
v___x_1338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = l_Std_Format_defWidth;
v___x_1341_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18);
v___x_1342_ = l_Std_Format_pretty(v___x_1341_, v___x_1340_, v___x_1339_, v___x_1339_);
return v___x_1342_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(lean_object* v_logger_1343_, lean_object* v_bctx_1344_, lean_object* v_out_1345_, lean_object* v_outputsFile_1346_){
_start:
{
lean_object* v___x_1354_; lean_object* v_outputsRef_x3f_1355_; 
v___x_1354_ = l_instMonadBaseIO;
v_outputsRef_x3f_1355_ = lean_ctor_get(v_bctx_1344_, 5);
lean_inc(v_outputsRef_x3f_1355_);
if (lean_obj_tag(v_outputsRef_x3f_1355_) == 1)
{
lean_object* v_toContext_1356_; lean_object* v_toBuildConfig_1357_; lean_object* v_val_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1505_; 
v_toContext_1356_ = lean_ctor_get(v_bctx_1344_, 1);
lean_inc(v_toContext_1356_);
v_toBuildConfig_1357_ = lean_ctor_get(v_bctx_1344_, 0);
lean_inc_ref(v_toBuildConfig_1357_);
lean_dec_ref(v_bctx_1344_);
v_val_1358_ = lean_ctor_get(v_outputsRef_x3f_1355_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_outputsRef_x3f_1355_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1360_ = v_outputsRef_x3f_1355_;
v_isShared_1361_ = v_isSharedCheck_1505_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_val_1358_);
lean_dec(v_outputsRef_x3f_1355_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1505_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_lakeEnv_1362_; lean_object* v_packages_1363_; uint8_t v_verbosity_1364_; lean_object* v_outputsIdx_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_lakeEnv_1362_ = lean_ctor_get(v_toContext_1356_, 0);
lean_inc_ref(v_lakeEnv_1362_);
v_packages_1363_ = lean_ctor_get(v_toContext_1356_, 4);
lean_inc_ref(v_packages_1363_);
lean_dec(v_toContext_1356_);
v_verbosity_1364_ = lean_ctor_get_uint8(v_toBuildConfig_1357_, sizeof(void*)*5 + 4);
v_outputsIdx_1365_ = lean_ctor_get(v_toBuildConfig_1357_, 2);
lean_inc(v_outputsIdx_1365_);
lean_dec_ref(v_toBuildConfig_1357_);
v___x_1366_ = lean_array_get_size(v_packages_1363_);
v___x_1367_ = lean_nat_dec_lt(v_outputsIdx_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v_putStr_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v_outputsIdx_1365_);
lean_dec_ref(v_packages_1363_);
lean_dec_ref(v_lakeEnv_1362_);
lean_del_object(v___x_1360_);
lean_dec(v_val_1358_);
lean_dec_ref(v_outputsFile_1346_);
lean_dec_ref(v_logger_1343_);
v_putStr_1368_ = lean_ctor_get(v_out_1345_, 4);
lean_inc_ref(v_putStr_1368_);
lean_dec_ref(v_out_1345_);
v___x_1369_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1370_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1371_ = lean_apply_2(v_putStr_1368_, v___x_1369_, lean_box(0));
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_dec_ref_known(v___x_1371_, 1);
goto v___jp_1350_;
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_2543__overap_1385_; lean_object* v___x_1386_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1374_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1375_ = lean_unsigned_to_nat(82u);
v___x_1376_ = lean_unsigned_to_nat(4u);
v___x_1377_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1378_ = lean_io_error_to_string(v_a_1372_);
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
v___x_1384_ = l_mkPanicMessageWithDecl(v___x_1373_, v___x_1374_, v___x_1375_, v___x_1376_, v___x_1383_);
lean_dec_ref(v___x_1383_);
v___x_2543__overap_1385_ = l_panic___redArg(v___x_1370_, v___x_1384_);
v___x_1386_ = lean_apply_1(v___x_2543__overap_1385_, lean_box(0));
lean_dec(v___x_1386_);
goto v___jp_1350_;
}
}
else
{
lean_object* v___x_1387_; lean_object* v_config_1388_; lean_object* v_enableArtifactCache_x3f_1389_; lean_object* v___f_1390_; lean_object* v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1394_; lean_object* v___y_1404_; lean_object* v___y_1405_; uint8_t v___y_1414_; uint8_t v___y_1483_; uint8_t v___y_1492_; 
v___x_1387_ = lean_array_fget(v_packages_1363_, v_outputsIdx_1365_);
lean_dec(v_outputsIdx_1365_);
v_config_1388_ = lean_ctor_get(v___x_1387_, 6);
v_enableArtifactCache_x3f_1389_ = lean_ctor_get(v_config_1388_, 24);
lean_inc_ref(v_logger_1343_);
v___f_1390_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1390_, 0, v_logger_1343_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1389_) == 0)
{
lean_object* v_enableArtifactCache_x3f_1493_; 
v_enableArtifactCache_x3f_1493_ = lean_ctor_get(v_lakeEnv_1362_, 6);
lean_inc(v_enableArtifactCache_x3f_1493_);
lean_dec_ref(v_lakeEnv_1362_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1493_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_config_1496_; lean_object* v_enableArtifactCache_x3f_1497_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_fget(v_packages_1363_, v___x_1494_);
lean_dec_ref(v_packages_1363_);
v_config_1496_ = lean_ctor_get(v___x_1495_, 6);
lean_inc_ref(v_config_1496_);
lean_dec(v___x_1495_);
v_enableArtifactCache_x3f_1497_ = lean_ctor_get(v_config_1496_, 24);
lean_inc(v_enableArtifactCache_x3f_1497_);
lean_dec_ref(v_config_1496_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1497_) == 0)
{
uint8_t v___x_1498_; 
v___x_1498_ = 0;
v___y_1483_ = v___x_1498_;
goto v___jp_1482_;
}
else
{
lean_object* v_val_1499_; uint8_t v___x_1500_; 
v_val_1499_ = lean_ctor_get(v_enableArtifactCache_x3f_1497_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1497_, 1);
v___x_1500_ = lean_unbox(v_val_1499_);
lean_dec(v_val_1499_);
v___y_1492_ = v___x_1500_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_val_1501_; uint8_t v___x_1502_; 
lean_dec_ref(v_packages_1363_);
v_val_1501_ = lean_ctor_get(v_enableArtifactCache_x3f_1493_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1493_, 1);
v___x_1502_ = lean_unbox(v_val_1501_);
lean_dec(v_val_1501_);
v___y_1492_ = v___x_1502_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_val_1503_; uint8_t v___x_1504_; 
lean_dec_ref(v_packages_1363_);
lean_dec_ref(v_lakeEnv_1362_);
v_val_1503_ = lean_ctor_get(v_enableArtifactCache_x3f_1389_, 0);
v___x_1504_ = lean_unbox(v_val_1503_);
v___y_1492_ = v___x_1504_;
goto v___jp_1491_;
}
v___jp_1391_:
{
if (v___y_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec_ref(v___y_1392_);
lean_dec_ref(v___f_1390_);
v___x_1395_ = lean_box(0);
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_array_get_size(v___y_1392_);
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_nat_dec_lt(v___y_1393_, v___x_1396_);
if (v___x_1398_ == 0)
{
lean_dec_ref(v___y_1392_);
lean_dec_ref(v___f_1390_);
return v___x_1397_;
}
else
{
size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_2357__overap_1401_; lean_object* v___x_1402_; 
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = lean_usize_of_nat(v___x_1396_);
v___x_2357__overap_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1354_, v___f_1390_, v___y_1392_, v___x_1399_, v___x_1400_, v___x_1397_);
v___x_1402_ = lean_apply_1(v___x_2357__overap_1401_, lean_box(0));
return v___x_1402_;
}
}
}
v___jp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = lean_array_get_size(v___y_1405_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_nat_dec_lt(v___y_1404_, v___x_1406_);
if (v___x_1408_ == 0)
{
lean_dec_ref(v___y_1405_);
lean_dec_ref(v___f_1390_);
return v___x_1407_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_2287__overap_1411_; lean_object* v___x_1412_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1406_);
v___x_2287__overap_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1354_, v___f_1390_, v___y_1405_, v___x_1409_, v___x_1410_, v___x_1407_);
v___x_1412_ = lean_apply_1(v___x_2287__overap_1411_, lean_box(0));
return v___x_1412_;
}
}
v___jp_1413_:
{
lean_object* v___x_1415_; lean_object* v_config_1416_; lean_object* v_toLeanConfig_1417_; lean_object* v_platformIndependent_1418_; lean_object* v___f_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1415_ = lean_st_ref_get(v_val_1358_);
lean_dec(v_val_1358_);
v_config_1416_ = lean_ctor_get(v___x_1387_, 6);
lean_inc_ref(v_config_1416_);
lean_dec(v___x_1387_);
v_toLeanConfig_1417_ = lean_ctor_get(v_config_1416_, 1);
lean_inc_ref(v_toLeanConfig_1417_);
lean_dec_ref(v_config_1416_);
v_platformIndependent_1418_ = lean_ctor_get(v_toLeanConfig_1417_, 10);
lean_inc(v_platformIndependent_1418_);
lean_dec_ref(v_toLeanConfig_1417_);
v___f_1419_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5));
v___x_1420_ = lean_box(v___x_1367_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1420_);
v___x_1422_ = v___x_1360_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = l_instBEqOption_beq___redArg(v___f_1419_, v_platformIndependent_1418_, v___x_1422_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_1426_ = l_Lake_CacheMap_writeFile(v_outputsFile_1346_, v___x_1415_, v___x_1423_, v___x_1425_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 1);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 2);
v___x_1428_ = lean_array_get_size(v_a_1427_);
v___x_1429_ = lean_nat_dec_eq(v___x_1428_, v___x_1424_);
if (v___x_1429_ == 0)
{
if (v___y_1414_ == 0)
{
lean_dec(v_a_1427_);
lean_dec_ref(v___f_1390_);
lean_dec_ref(v_out_1345_);
goto v___jp_1348_;
}
else
{
lean_object* v_putStr_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_putStr_1430_ = lean_ctor_get(v_out_1345_, 4);
lean_inc_ref(v_putStr_1430_);
lean_dec_ref(v_out_1345_);
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1432_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1433_ = lean_apply_2(v_putStr_1430_, v___x_1431_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref_known(v___x_1433_, 1);
v___y_1404_ = v___x_1424_;
v___y_1405_ = v_a_1427_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_2551__overap_1452_; lean_object* v___x_1453_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1436_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1437_ = lean_unsigned_to_nat(82u);
v___x_1438_ = lean_unsigned_to_nat(4u);
v___x_1439_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1440_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1441_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1440_, v___y_1414_);
v___x_1442_ = lean_string_append(v___x_1439_, v___x_1441_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1444_ = lean_string_append(v___x_1442_, v___x_1443_);
v___x_1445_ = lean_io_error_to_string(v_a_1434_);
v___x_1446_ = lean_string_append(v___x_1444_, v___x_1445_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1448_ = lean_string_append(v___x_1446_, v___x_1447_);
v___x_1449_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
v___x_1451_ = l_mkPanicMessageWithDecl(v___x_1435_, v___x_1436_, v___x_1437_, v___x_1438_, v___x_1450_);
lean_dec_ref(v___x_1450_);
v___x_2551__overap_1452_ = l_panic___redArg(v___x_1432_, v___x_1451_);
v___x_1453_ = lean_apply_1(v___x_2551__overap_1452_, lean_box(0));
lean_dec(v___x_1453_);
v___y_1404_ = v___x_1424_;
v___y_1405_ = v_a_1427_;
goto v___jp_1403_;
}
}
}
else
{
lean_dec(v_a_1427_);
lean_dec_ref(v___f_1390_);
lean_dec_ref(v_out_1345_);
goto v___jp_1348_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v_putStr_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_a_1454_ = lean_ctor_get(v___x_1426_, 1);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1426_, 2);
v_putStr_1455_ = lean_ctor_get(v_out_1345_, 4);
lean_inc_ref(v_putStr_1455_);
lean_dec_ref(v_out_1345_);
v___x_1456_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1457_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1458_ = lean_apply_2(v_putStr_1455_, v___x_1456_, lean_box(0));
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_dec_ref_known(v___x_1458_, 1);
v___y_1392_ = v_a_1454_;
v___y_1393_ = v___x_1424_;
v___y_1394_ = v___y_1414_;
goto v___jp_1391_;
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_2556__overap_1477_; lean_object* v___x_1478_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1461_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1462_ = lean_unsigned_to_nat(82u);
v___x_1463_ = lean_unsigned_to_nat(4u);
v___x_1464_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1465_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1465_, v___x_1367_);
v___x_1467_ = lean_string_append(v___x_1464_, v___x_1466_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1469_ = lean_string_append(v___x_1467_, v___x_1468_);
v___x_1470_ = lean_io_error_to_string(v_a_1459_);
v___x_1471_ = lean_string_append(v___x_1469_, v___x_1470_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1473_ = lean_string_append(v___x_1471_, v___x_1472_);
v___x_1474_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_1475_ = lean_string_append(v___x_1473_, v___x_1474_);
v___x_1476_ = l_mkPanicMessageWithDecl(v___x_1460_, v___x_1461_, v___x_1462_, v___x_1463_, v___x_1475_);
lean_dec_ref(v___x_1475_);
v___x_2556__overap_1477_ = l_panic___redArg(v___x_1457_, v___x_1476_);
v___x_1478_ = lean_apply_1(v___x_2556__overap_1477_, lean_box(0));
lean_dec(v___x_1478_);
v___y_1392_ = v_a_1454_;
v___y_1393_ = v___x_1424_;
v___y_1394_ = v___y_1414_;
goto v___jp_1391_;
}
}
}
}
v___jp_1480_:
{
if (v_verbosity_1364_ == 2)
{
v___y_1414_ = v___x_1367_;
goto v___jp_1413_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
v___y_1414_ = v___x_1481_;
goto v___jp_1413_;
}
}
v___jp_1482_:
{
lean_object* v_baseName_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_baseName_1484_ = lean_ctor_get(v___x_1387_, 1);
lean_inc(v_baseName_1484_);
v___x_1485_ = l_Lean_Name_toString(v_baseName_1484_, v___y_1483_);
v___x_1486_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_1487_ = lean_string_append(v___x_1485_, v___x_1486_);
v___x_1488_ = 2;
v___x_1489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*1, v___x_1488_);
v___x_1490_ = lean_apply_2(v_logger_1343_, v___x_1489_, lean_box(0));
goto v___jp_1480_;
}
v___jp_1491_:
{
if (v___y_1492_ == 0)
{
v___y_1483_ = v___y_1492_;
goto v___jp_1482_;
}
else
{
lean_dec_ref(v_logger_1343_);
goto v___jp_1480_;
}
}
}
}
}
else
{
lean_object* v_putStr_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_outputsRef_x3f_1355_);
lean_dec_ref(v_outputsFile_1346_);
lean_dec_ref(v_bctx_1344_);
lean_dec_ref(v_logger_1343_);
v_putStr_1506_ = lean_ctor_get(v_out_1345_, 4);
lean_inc_ref(v_putStr_1506_);
lean_dec_ref(v_out_1345_);
v___x_1507_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1508_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1509_ = lean_apply_2(v_putStr_1506_, v___x_1507_, lean_box(0));
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref_known(v___x_1509_, 1);
goto v___jp_1352_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_2561__overap_1523_; lean_object* v___x_1524_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1512_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1513_ = lean_unsigned_to_nat(82u);
v___x_1514_ = lean_unsigned_to_nat(4u);
v___x_1515_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1516_ = lean_io_error_to_string(v_a_1510_);
v___x_1517_ = lean_string_append(v___x_1515_, v___x_1516_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
v___x_1520_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
v___x_1522_ = l_mkPanicMessageWithDecl(v___x_1511_, v___x_1512_, v___x_1513_, v___x_1514_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_2561__overap_1523_ = l_panic___redArg(v___x_1508_, v___x_1522_);
v___x_1524_ = lean_apply_1(v___x_2561__overap_1523_, lean_box(0));
lean_dec(v___x_1524_);
goto v___jp_1352_;
}
}
v___jp_1348_:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
v___jp_1350_:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
v___jp_1352_:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs_0interp(lean_interpreter_value* stack)
{
lean_object* v_logger_1343_ = stack[0].m_obj;
lean_object* v_bctx_1344_ = stack[1].m_obj;
lean_object* v_out_1345_ = stack[2].m_obj;
lean_object* v_outputsFile_1346_ = stack[3].m_obj;
lean_object* v_res_1525_;
v_res_1525_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(v_logger_1343_, v_bctx_1344_, v_out_1345_, v_outputsFile_1346_);
stack->m_obj
 = v_res_1525_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___boxed(lean_object* v_logger_1526_, lean_object* v_bctx_1527_, lean_object* v_out_1528_, lean_object* v_outputsFile_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(v_logger_1526_, v_bctx_1527_, v_out_1528_, v_outputsFile_1529_);
return v_res_1531_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1533_, lean_object* v_as_1534_, size_t v_i_1535_, size_t v_stop_1536_, lean_object* v_b_1537_){
_start:
{
lean_object* v_val_1540_; uint8_t v___x_1544_; 
v___x_1544_ = lean_usize_dec_eq(v_i_1535_, v_stop_1536_);
if (v___x_1544_ == 0)
{
lean_object* v_putStr_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_putStr_1545_ = lean_ctor_get(v_out_1533_, 4);
v___x_1546_ = lean_array_uget_borrowed(v_as_1534_, v_i_1535_);
v___x_1547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1548_ = lean_string_append(v___x_1547_, v___x_1546_);
v___x_1549_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1550_ = lean_string_append(v___x_1548_, v___x_1549_);
lean_inc_ref(v_putStr_1545_);
lean_inc_ref(v___x_1550_);
v___x_1551_ = lean_apply_2(v_putStr_1545_, v___x_1550_, lean_box(0));
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; 
lean_dec_ref(v___x_1550_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v_val_1540_ = v_a_1552_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1576_; 
v_a_1553_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1555_ = v___x_1551_;
v_isShared_1556_ = v_isSharedCheck_1576_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1551_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1576_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1557_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1558_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1559_ = lean_unsigned_to_nat(82u);
v___x_1560_ = lean_unsigned_to_nat(4u);
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1563_ = lean_io_error_to_string(v_a_1553_);
v___x_1564_ = lean_string_append(v___x_1562_, v___x_1563_);
lean_dec_ref(v___x_1563_);
v___x_1565_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1566_ = lean_string_append(v___x_1564_, v___x_1565_);
v___x_1567_ = l_String_quote(v___x_1550_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 3);
lean_ctor_set(v___x_1555_, 0, v___x_1567_);
v___x_1569_ = v___x_1555_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1570_ = l_Std_Format_defWidth;
v___x_1571_ = l_Std_Format_pretty(v___x_1569_, v___x_1570_, v___x_1561_, v___x_1561_);
v___x_1572_ = lean_string_append(v___x_1566_, v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = l_mkPanicMessageWithDecl(v___x_1557_, v___x_1558_, v___x_1559_, v___x_1560_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1573_);
v_val_1540_ = v___x_1574_;
goto v___jp_1539_;
}
}
}
}
else
{
lean_dec_ref(v_out_1533_);
return v_b_1537_;
}
v___jp_1539_:
{
size_t v___x_1541_; size_t v___x_1542_; 
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_add(v_i_1535_, v___x_1541_);
v_i_1535_ = v___x_1542_;
v_b_1537_ = v_val_1540_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_out_1533_ = stack[0].m_obj;
lean_object* v_as_1534_ = stack[1].m_obj;
size_t v_i_1535_ = stack[2].m_num;
size_t v_stop_1536_ = stack[3].m_num;
lean_object* v_b_1537_ = stack[4].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1533_, v_as_1534_, v_i_1535_, v_stop_1536_, v_b_1537_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1578_, lean_object* v_as_1579_, lean_object* v_i_1580_, lean_object* v_stop_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_){
_start:
{
size_t v_i_boxed_1584_; size_t v_stop_boxed_1585_; lean_object* v_res_1586_; 
v_i_boxed_1584_ = lean_unbox_usize(v_i_1580_);
lean_dec(v_i_1580_);
v_stop_boxed_1585_ = lean_unbox_usize(v_stop_1581_);
lean_dec(v_stop_1581_);
v_res_1586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1578_, v_as_1579_, v_i_boxed_1584_, v_stop_boxed_1585_, v_b_1582_);
lean_dec_ref(v_as_1579_);
return v_res_1586_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1594_ = l_String_quote(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = l_Std_Format_defWidth;
v___x_1599_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1600_ = l_Std_Format_pretty(v___x_1599_, v___x_1598_, v___x_1597_, v___x_1597_);
return v___x_1600_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1603_ = l_String_quote(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = l_Std_Format_defWidth;
v___x_1608_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1609_ = l_Std_Format_pretty(v___x_1608_, v___x_1607_, v___x_1606_, v___x_1606_);
return v___x_1609_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1610_, lean_object* v_out_1611_, lean_object* v_result_1612_){
_start:
{
uint8_t v___y_1615_; lean_object* v___y_1616_; lean_object* v_failures_1690_; lean_object* v_numJobs_1691_; uint8_t v___y_1693_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_failures_1690_ = lean_ctor_get(v_result_1612_, 0);
lean_inc_ref(v_failures_1690_);
v_numJobs_1691_ = lean_ctor_get(v_result_1612_, 1);
lean_inc(v_numJobs_1691_);
lean_dec_ref(v_result_1612_);
v___x_1726_ = lean_array_get_size(v_failures_1690_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_nat_dec_eq(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v_flush_1729_; lean_object* v_putStr_1730_; lean_object* v___y_1736_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_numJobs_1691_);
v_flush_1729_ = lean_ctor_get(v_out_1611_, 0);
lean_inc_ref(v_flush_1729_);
v_putStr_1730_ = lean_ctor_get(v_out_1611_, 4);
v___x_1747_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1730_);
v___x_1748_ = lean_apply_2(v_putStr_1730_, v___x_1747_, lean_box(0));
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec_ref_known(v___x_1748_, 1);
goto v___jp_1737_;
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1751_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1752_ = lean_unsigned_to_nat(82u);
v___x_1753_ = lean_unsigned_to_nat(4u);
v___x_1754_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1755_ = lean_io_error_to_string(v_a_1749_);
v___x_1756_ = lean_string_append(v___x_1754_, v___x_1755_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
v___x_1759_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1760_ = lean_string_append(v___x_1758_, v___x_1759_);
v___x_1761_ = l_mkPanicMessageWithDecl(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1753_, v___x_1760_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1761_);
goto v___jp_1737_;
}
v___jp_1731_:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_apply_1(v_flush_1729_, lean_box(0));
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
return v_a_1733_;
}
else
{
lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = lean_box(0);
return v___x_1734_;
}
}
v___jp_1735_:
{
goto v___jp_1731_;
}
v___jp_1737_:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_nat_dec_lt(v___x_1727_, v___x_1726_);
if (v___x_1738_ == 0)
{
lean_dec_ref(v_failures_1690_);
lean_dec_ref(v_out_1611_);
goto v___jp_1731_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_nat_dec_le(v___x_1726_, v___x_1726_);
if (v___x_1740_ == 0)
{
if (v___x_1738_ == 0)
{
lean_dec_ref(v_failures_1690_);
lean_dec_ref(v_out_1611_);
goto v___jp_1731_;
}
else
{
size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = lean_usize_of_nat(v___x_1726_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1611_, v_failures_1690_, v___x_1741_, v___x_1742_, v___x_1739_);
lean_dec_ref(v_failures_1690_);
v___y_1736_ = v___x_1743_;
goto v___jp_1735_;
}
}
else
{
size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = lean_usize_of_nat(v___x_1726_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1611_, v_failures_1690_, v___x_1744_, v___x_1745_, v___x_1739_);
lean_dec_ref(v_failures_1690_);
v___y_1736_ = v___x_1746_;
goto v___jp_1735_;
}
}
}
}
else
{
uint8_t v___x_1763_; 
lean_dec_ref(v_failures_1690_);
v___x_1763_ = l_Lake_BuildConfig_showProgress(v_cfg_1610_);
if (v___x_1763_ == 0)
{
v___y_1693_ = v___x_1763_;
goto v___jp_1692_;
}
else
{
uint8_t v_showSuccess_1764_; 
v_showSuccess_1764_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*5 + 5);
v___y_1693_ = v_showSuccess_1764_;
goto v___jp_1692_;
}
}
v___jp_1614_:
{
uint8_t v_noBuild_1617_; 
v_noBuild_1617_ = lean_ctor_get_uint8(v_cfg_1610_, sizeof(void*)*5 + 2);
if (v_noBuild_1617_ == 0)
{
lean_object* v_putStr_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_putStr_1618_ = lean_ctor_get(v_out_1611_, 4);
lean_inc_ref(v_putStr_1618_);
lean_dec_ref(v_out_1611_);
v___x_1619_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1620_ = lean_string_append(v___x_1619_, v___y_1616_);
lean_dec_ref(v___y_1616_);
v___x_1621_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1622_ = lean_string_append(v___x_1620_, v___x_1621_);
lean_inc_ref(v___x_1622_);
v___x_1623_ = lean_apply_2(v_putStr_1618_, v___x_1622_, lean_box(0));
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; 
lean_dec_ref(v___x_1622_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
return v_a_1624_;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1653_; 
v_a_1625_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1627_ = v___x_1623_;
v_isShared_1628_ = v_isSharedCheck_1653_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1653_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1629_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1630_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1631_ = lean_unsigned_to_nat(82u);
v___x_1632_ = lean_unsigned_to_nat(4u);
v___x_1633_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1635_, v___y_1615_);
v___x_1637_ = lean_string_append(v___x_1633_, v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1639_ = lean_string_append(v___x_1637_, v___x_1638_);
v___x_1640_ = lean_io_error_to_string(v_a_1625_);
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1643_ = lean_string_append(v___x_1641_, v___x_1642_);
v___x_1644_ = l_String_quote(v___x_1622_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 3);
lean_ctor_set(v___x_1627_, 0, v___x_1644_);
v___x_1646_ = v___x_1627_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1647_ = l_Std_Format_defWidth;
v___x_1648_ = l_Std_Format_pretty(v___x_1646_, v___x_1647_, v___x_1634_, v___x_1634_);
v___x_1649_ = lean_string_append(v___x_1643_, v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l_mkPanicMessageWithDecl(v___x_1629_, v___x_1630_, v___x_1631_, v___x_1632_, v___x_1649_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1650_);
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_putStr_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_putStr_1654_ = lean_ctor_get(v_out_1611_, 4);
lean_inc_ref(v_putStr_1654_);
lean_dec_ref(v_out_1611_);
v___x_1655_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1656_ = lean_string_append(v___x_1655_, v___y_1616_);
lean_dec_ref(v___y_1616_);
v___x_1657_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1658_ = lean_string_append(v___x_1656_, v___x_1657_);
lean_inc_ref(v___x_1658_);
v___x_1659_ = lean_apply_2(v_putStr_1654_, v___x_1658_, lean_box(0));
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; 
lean_dec_ref(v___x_1658_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
return v_a_1660_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1689_; 
v_a_1661_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1689_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1689_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1665_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1666_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1667_ = lean_unsigned_to_nat(82u);
v___x_1668_ = lean_unsigned_to_nat(4u);
v___x_1669_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1672_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1671_, v_noBuild_1617_);
v___x_1673_ = lean_string_append(v___x_1669_, v___x_1672_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1675_ = lean_string_append(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_io_error_to_string(v_a_1661_);
v___x_1677_ = lean_string_append(v___x_1675_, v___x_1676_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1679_ = lean_string_append(v___x_1677_, v___x_1678_);
v___x_1680_ = l_String_quote(v___x_1658_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 3);
lean_ctor_set(v___x_1663_, 0, v___x_1680_);
v___x_1682_ = v___x_1663_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1683_ = l_Std_Format_defWidth;
v___x_1684_ = l_Std_Format_pretty(v___x_1682_, v___x_1683_, v___x_1670_, v___x_1670_);
v___x_1685_ = lean_string_append(v___x_1679_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_mkPanicMessageWithDecl(v___x_1665_, v___x_1666_, v___x_1667_, v___x_1668_, v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1686_);
return v___x_1687_;
}
}
}
}
}
v___jp_1692_:
{
if (v___y_1693_ == 0)
{
lean_object* v___x_1694_; 
lean_dec(v_numJobs_1691_);
lean_dec_ref(v_out_1611_);
v___x_1694_ = lean_box(0);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = lean_nat_dec_eq(v_numJobs_1691_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_dec_eq(v_numJobs_1691_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = l_Nat_reprFast(v_numJobs_1691_);
v___x_1700_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1701_ = lean_string_append(v___x_1699_, v___x_1700_);
v___y_1615_ = v___y_1693_;
v___y_1616_ = v___x_1701_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1702_; 
lean_dec(v_numJobs_1691_);
v___x_1702_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1615_ = v___y_1693_;
v___y_1616_ = v___x_1702_;
goto v___jp_1614_;
}
}
else
{
lean_object* v_putStr_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v_numJobs_1691_);
v_putStr_1703_ = lean_ctor_get(v_out_1611_, 4);
lean_inc_ref(v_putStr_1703_);
lean_dec_ref(v_out_1611_);
v___x_1704_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1705_ = lean_apply_2(v_putStr_1703_, v___x_1704_, lean_box(0));
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
return v_a_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1707_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1708_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1709_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1710_ = lean_unsigned_to_nat(82u);
v___x_1711_ = lean_unsigned_to_nat(4u);
v___x_1712_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1713_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1714_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1713_, v___x_1696_);
v___x_1715_ = lean_string_append(v___x_1712_, v___x_1714_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1717_ = lean_string_append(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_io_error_to_string(v_a_1707_);
v___x_1719_ = lean_string_append(v___x_1717_, v___x_1718_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
v___x_1722_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
v___x_1724_ = l_mkPanicMessageWithDecl(v___x_1708_, v___x_1709_, v___x_1710_, v___x_1711_, v___x_1723_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1724_);
return v___x_1725_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_reportResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1610_ = stack[0].m_obj;
lean_object* v_out_1611_ = stack[1].m_obj;
lean_object* v_result_1612_ = stack[2].m_obj;
lean_object* v_res_1765_;
v_res_1765_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1610_, v_out_1611_, v_result_1612_);
stack->m_obj
 = v_res_1765_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1766_, lean_object* v_out_1767_, lean_object* v_result_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1766_, v_out_1767_, v_result_1768_);
lean_dec_ref(v_cfg_1766_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(lean_object* v_self_1771_){
_start:
{
lean_object* v_toMonitorResult_1772_; 
v_toMonitorResult_1772_ = lean_ctor_get(v_self_1771_, 0);
lean_inc_ref(v_toMonitorResult_1772_);
return v_toMonitorResult_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0___boxed(lean_object* v_self_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(v_self_1773_);
lean_dec_ref(v_self_1773_);
return v_res_1774_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg(){
_start:
{
lean_object* v___f_1777_; 
v___f_1777_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1777_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1778_;
v_res_1778_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg();
stack->m_obj
 = v_res_1778_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___boxed(lean_object* v___dummy_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg();
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1781_){
_start:
{
lean_object* v___f_1782_; 
v___f_1782_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1782_;
}
}
uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1783_){
_start:
{
lean_object* v_out_1784_; 
v_out_1784_ = lean_ctor_get(v_self_1783_, 1);
if (lean_obj_tag(v_out_1784_) == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = 0;
return v___x_1785_;
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = 1;
return v___x_1786_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1783_ = stack[0].m_obj;
uint8_t v_res_1787_;
v_res_1787_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1783_);
stack->m_num = v_res_1787_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1788_){
_start:
{
uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_res_1789_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1788_);
lean_dec_ref(v_self_1788_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1791_, lean_object* v_self_1792_){
_start:
{
lean_object* v_out_1793_; 
v_out_1793_ = lean_ctor_get(v_self_1792_, 1);
if (lean_obj_tag(v_out_1793_) == 0)
{
uint8_t v___x_1794_; 
v___x_1794_ = 0;
return v___x_1794_;
}
else
{
uint8_t v___x_1795_; 
v___x_1795_ = 1;
return v___x_1795_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_BuildResult_isOk_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1792_ = stack[1].m_obj;
uint8_t v_res_1796_;
v_res_1796_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_box(0), v_self_1792_);
stack->m_num = v_res_1796_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_self_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1797_, v_self_1798_);
lean_dec_ref(v_self_1798_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1809_, lean_object* v_job_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_failures_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
lean_inc_ref(v_job_1810_);
v___x_1812_ = l_Lake_Job_toOpaque___redArg(v_job_1810_);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = lean_mk_empty_array_with_capacity(v___x_1813_);
v___x_1815_ = lean_array_push(v___x_1814_, v___x_1812_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1818_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1819_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1809_, v___x_1815_, v___x_1817_, v___x_1818_);
v_failures_1820_ = lean_ctor_get(v___x_1819_, 0);
v___x_1821_ = lean_array_get_size(v_failures_1820_);
v___x_1822_ = lean_nat_dec_eq(v___x_1821_, v___x_1816_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v_job_1810_);
v___x_1823_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1819_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v_task_1825_; lean_object* v___x_1826_; 
v_task_1825_ = lean_ctor_get(v_job_1810_, 0);
lean_inc_ref(v_task_1825_);
lean_dec_ref(v_job_1810_);
v___x_1826_ = lean_io_wait(v_task_1825_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1835_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v___x_1826_, 1);
lean_dec(v_unused_1836_);
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_a_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1831_);
lean_ctor_set(v___x_1829_, 0, v___x_1819_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; lean_object* v_unused_1846_; 
v_unused_1845_ = lean_ctor_get(v___x_1826_, 1);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v___x_1826_, 0);
lean_dec(v_unused_1846_);
v___x_1838_ = v___x_1826_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_dec(v___x_1826_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 0);
lean_ctor_set(v___x_1838_, 1, v___x_1840_);
lean_ctor_set(v___x_1838_, 0, v___x_1819_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_monitorJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1809_ = stack[0].m_obj;
lean_object* v_job_1810_ = stack[1].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1809_, v_job_1810_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1848_, lean_object* v_job_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1848_, v_job_1849_);
lean_dec_ref(v_ctx_1848_);
return v_res_1851_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1852_, lean_object* v_ctx_1853_, lean_object* v_job_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1853_, v_job_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_monitorJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1853_ = stack[1].m_obj;
lean_object* v_job_1854_ = stack[2].m_obj;
lean_object* v_res_1857_;
v_res_1857_ = l___private_Lake_Build_Run_0__Lake_monitorJob(lean_box(0), v_ctx_1853_, v_job_1854_);
stack->m_obj
 = v_res_1857_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_ctx_1859_, lean_object* v_job_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1858_, v_ctx_1859_, v_job_1860_);
lean_dec_ref(v_ctx_1859_);
return v_res_1862_;
}
}
lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object* v_info_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lake_computeTextFileHash(v_info_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = lean_io_metadata(v_info_1865_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1881_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1881_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1881_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_modified_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint64_t v___x_1877_; lean_object* v___x_1879_; 
v_modified_1874_ = lean_ctor_get(v_a_1870_, 1);
lean_inc_ref(v_modified_1874_);
lean_dec(v_a_1870_);
v___x_1875_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1876_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1876_, 0, v_info_1865_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
lean_ctor_set(v___x_1876_, 2, v_modified_1874_);
v___x_1877_ = lean_unbox_uint64(v_a_1868_);
lean_dec(v_a_1868_);
lean_ctor_set_uint64(v___x_1876_, sizeof(void*)*3, v___x_1877_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1876_);
v___x_1879_ = v___x_1872_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1876_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_a_1868_);
lean_dec_ref(v_info_1865_);
v_a_1882_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1869_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1869_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_info_1865_);
v_a_1890_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1867_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1867_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1865_ = stack[0].m_obj;
lean_object* v_res_1898_;
v_res_1898_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1865_);
stack->m_obj
 = v_res_1898_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object* v_info_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1899_);
return v_res_1901_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object* v___x_1905_, lean_object* v_as_1906_, size_t v_sz_1907_, size_t v_i_1908_, lean_object* v_b_1909_){
_start:
{
lean_object* v_a_1912_; uint8_t v___x_1916_; 
v___x_1916_ = lean_usize_dec_lt(v_i_1908_, v_sz_1907_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v___x_1905_);
return v_b_1909_;
}
else
{
lean_object* v_snd_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1940_; 
v_snd_1917_ = lean_ctor_get(v_b_1909_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_b_1909_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_b_1909_, 0);
lean_dec(v_unused_1941_);
v___x_1919_ = v_b_1909_;
v_isShared_1920_ = v_isSharedCheck_1940_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snd_1917_);
lean_dec(v_b_1909_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1940_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1921_ = lean_box(0);
v_a_1922_ = lean_array_uget_borrowed(v_as_1906_, v_i_1908_);
v___x_1923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0));
lean_inc_ref(v___x_1905_);
v___x_1924_ = l_Lake_joinRelative(v___x_1905_, v___x_1923_);
lean_inc(v_a_1922_);
v___x_1925_ = l_Lake_joinRelative(v___x_1924_, v_a_1922_);
v___x_1926_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v___x_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = l_Lake_BuildTrace_mix(v_snd_1917_, v_a_1927_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1928_);
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v_a_1912_ = v___x_1930_;
goto v___jp_1911_;
}
}
else
{
lean_object* v_a_1932_; 
v_a_1932_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1926_, 1);
if (lean_obj_tag(v_a_1932_) == 11)
{
lean_object* v___x_1934_; 
lean_dec_ref_known(v_a_1932_, 2);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1934_ = v___x_1919_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_snd_1917_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
v_a_1912_ = v___x_1934_;
goto v___jp_1911_;
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_dec(v_a_1932_);
lean_dec_ref(v___x_1905_);
v___x_1936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1));
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1936_);
v___x_1938_ = v___x_1919_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_snd_1917_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
v___jp_1911_:
{
size_t v___x_1913_; size_t v___x_1914_; 
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1908_, v___x_1913_);
v_i_1908_ = v___x_1914_;
v_b_1909_ = v_a_1912_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1905_ = stack[0].m_obj;
lean_object* v_as_1906_ = stack[1].m_obj;
size_t v_sz_1907_ = stack[2].m_num;
size_t v_i_1908_ = stack[3].m_num;
lean_object* v_b_1909_ = stack[4].m_obj;
lean_object* v_res_1942_;
v_res_1942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1905_, v_as_1906_, v_sz_1907_, v_i_1908_, v_b_1909_);
stack->m_obj
 = v_res_1942_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object* v___x_1943_, lean_object* v_as_1944_, lean_object* v_sz_1945_, lean_object* v_i_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_){
_start:
{
size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1945_);
lean_dec(v_sz_1945_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1946_);
lean_dec(v_i_1946_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1943_, v_as_1944_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1951_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1));
v___x_1955_ = l_Lake_BuildTrace_nil(v___x_1954_);
return v___x_1955_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2);
v___x_1971_ = lean_box(0);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1970_);
return v___x_1972_;
}
}
static size_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1973_; size_t v_sz_1974_; 
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v_sz_1974_ = lean_array_size(v___x_1973_);
return v_sz_1974_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t v_sz_1975_, size_t v_i_1976_, lean_object* v_bs_1977_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
if (v___x_1979_ == 0)
{
return v_bs_1977_;
}
else
{
lean_object* v_v_1980_; lean_object* v_config_1981_; lean_object* v_dir_1982_; uint8_t v_bootstrap_1983_; lean_object* v_buildDir_1984_; lean_object* v___x_1985_; lean_object* v_bs_x27_1986_; lean_object* v_val_1988_; 
v_v_1980_ = lean_array_uget_borrowed(v_bs_1977_, v_i_1976_);
v_config_1981_ = lean_ctor_get(v_v_1980_, 6);
v_dir_1982_ = lean_ctor_get(v_v_1980_, 4);
lean_inc_ref(v_dir_1982_);
v_bootstrap_1983_ = lean_ctor_get_uint8(v_config_1981_, sizeof(void*)*28);
v_buildDir_1984_ = lean_ctor_get(v_config_1981_, 5);
lean_inc_ref(v_buildDir_1984_);
v___x_1985_ = lean_unsigned_to_nat(0u);
v_bs_x27_1986_ = lean_array_uset(v_bs_1977_, v_i_1976_, v___x_1985_);
if (v_bootstrap_1983_ == 0)
{
lean_object* v___x_1993_; 
lean_dec_ref(v_buildDir_1984_);
lean_dec_ref(v_dir_1982_);
v___x_1993_ = lean_box(0);
v_val_1988_ = v___x_1993_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; size_t v_sz_2000_; size_t v___x_2001_; lean_object* v___x_2002_; lean_object* v_fst_2003_; 
v___x_1994_ = l_System_FilePath_normalize(v_buildDir_1984_);
v___x_1995_ = l_Lake_joinRelative(v_dir_1982_, v___x_1994_);
v___x_1996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0));
v___x_1997_ = l_Lake_joinRelative(v___x_1995_, v___x_1996_);
v___x_1998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v___x_1999_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8);
v_sz_2000_ = lean_usize_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9);
v___x_2001_ = ((size_t)0ULL);
lean_inc_ref(v___x_1997_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1997_, v___x_1998_, v_sz_2000_, v___x_2001_, v___x_1999_);
v_fst_2003_ = lean_ctor_get(v___x_2002_, 0);
if (lean_obj_tag(v_fst_2003_) == 0)
{
lean_object* v_snd_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2012_; 
v_snd_2004_ = lean_ctor_get(v___x_2002_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_2002_, 0);
lean_dec(v_unused_2013_);
v___x_2006_ = v___x_2002_;
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2004_);
lean_dec(v___x_2002_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_1997_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_snd_2004_);
v___x_2009_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
v_val_1988_ = v___x_2010_;
goto v___jp_1987_;
}
}
}
else
{
lean_object* v_val_2014_; 
lean_inc_ref(v_fst_2003_);
lean_dec_ref(v___x_2002_);
lean_dec_ref(v___x_1997_);
v_val_2014_ = lean_ctor_get(v_fst_2003_, 0);
lean_inc(v_val_2014_);
lean_dec_ref_known(v_fst_2003_, 1);
v_val_1988_ = v_val_2014_;
goto v___jp_1987_;
}
}
v___jp_1987_:
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1976_, v___x_1989_);
v___x_1991_ = lean_array_uset(v_bs_x27_1986_, v_i_1976_, v_val_1988_);
v_i_1976_ = v___x_1990_;
v_bs_1977_ = v___x_1991_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1975_ = stack[0].m_num;
size_t v_i_1976_ = stack[1].m_num;
lean_object* v_bs_1977_ = stack[2].m_obj;
lean_object* v_res_2015_;
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_1975_, v_i_1976_, v_bs_1977_);
stack->m_obj
 = v_res_2015_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object* v_sz_2016_, lean_object* v_i_2017_, lean_object* v_bs_2018_, lean_object* v___y_2019_){
_start:
{
size_t v_sz_boxed_2020_; size_t v_i_boxed_2021_; lean_object* v_res_2022_; 
v_sz_boxed_2020_ = lean_unbox_usize(v_sz_2016_);
lean_dec(v_sz_2016_);
v_i_boxed_2021_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_boxed_2020_, v_i_boxed_2021_, v_bs_2018_);
return v_res_2022_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = l_Lean_versionStringCore;
v___x_2025_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0));
v___x_2026_ = lean_string_append(v___x_2025_, v___x_2024_);
return v___x_2026_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2));
v___x_2029_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1);
v___x_2030_ = lean_string_append(v___x_2029_, v___x_2028_);
return v___x_2030_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_nat_to_int(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5(void){
_start:
{
uint32_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = 0;
v___x_2034_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4);
v___x_2035_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set_uint32(v___x_2035_, sizeof(void*)*1, v___x_2033_);
return v___x_2035_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_unsigned_to_nat(16u);
v___x_2038_ = lean_mk_array(v___x_2037_, v___x_2036_);
return v___x_2038_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6);
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
return v___x_2041_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object* v_ws_2044_, lean_object* v_cfg_2045_, lean_object* v_jobs_2046_, lean_object* v_cancelTk_x3f_2047_){
_start:
{
lean_object* v___y_2050_; uint8_t v___y_2051_; uint8_t v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; uint8_t v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2059_; uint8_t v___y_2060_; lean_object* v_val_2061_; lean_object* v___y_2079_; uint8_t v___y_2080_; uint8_t v___y_2081_; uint8_t v___y_2082_; lean_object* v___y_2083_; uint8_t v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; lean_object* v_val_2092_; uint8_t v___x_2118_; 
v___x_2118_ = l_System_Platform_isOSX;
if (v___x_2118_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_2119_; 
v_macosxDeploymentTarget_x3f_2119_ = lean_ctor_get(v_cfg_2045_, 4);
lean_inc(v_macosxDeploymentTarget_x3f_2119_);
v_val_2092_ = v_macosxDeploymentTarget_x3f_2119_;
goto v___jp_2091_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_2120_; 
v_macosxDeploymentTarget_x3f_2120_ = lean_ctor_get(v_cfg_2045_, 4);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_2120_) == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___y_2124_; 
v___x_2121_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8));
v___x_2122_ = lean_io_getenv(v___x_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9));
v___y_2124_ = v___x_2126_;
goto v___jp_2123_;
}
else
{
lean_object* v_val_2127_; 
v_val_2127_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2122_, 1);
v___y_2124_ = v_val_2127_;
goto v___jp_2123_;
}
v___jp_2123_:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___y_2124_);
v_val_2092_ = v___x_2125_;
goto v___jp_2091_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_2120_);
v_val_2092_ = v_macosxDeploymentTarget_x3f_2120_;
goto v___jp_2091_;
}
}
v___jp_2049_:
{
lean_object* v_lakeEnv_2062_; lean_object* v_packages_2063_; size_t v_sz_2064_; size_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_lakeEnv_2062_ = lean_ctor_get(v_ws_2044_, 0);
v_packages_2063_ = lean_ctor_get(v_ws_2044_, 4);
v_sz_2064_ = lean_array_size(v_packages_2063_);
v___x_2065_ = ((size_t)0ULL);
lean_inc_ref(v_packages_2063_);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_2064_, v___x_2065_, v_packages_2063_);
v___x_2067_ = lean_alloc_ctor(0, 5, 6);
lean_ctor_set(v___x_2067_, 0, v___y_2050_);
lean_ctor_set(v___x_2067_, 1, v___y_2059_);
lean_ctor_set(v___x_2067_, 2, v___y_2055_);
lean_ctor_set(v___x_2067_, 3, v___y_2053_);
lean_ctor_set(v___x_2067_, 4, v___y_2057_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5, v___y_2051_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 1, v___y_2052_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 2, v___y_2060_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 3, v___y_2056_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 4, v___y_2058_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*5 + 5, v___y_2054_);
v___x_2068_ = l_Lake_Env_leanGithash(v_lakeEnv_2062_);
v___x_2069_ = l_Lake_Hash_nil;
v___x_2070_ = lean_string_hash(v___x_2068_);
v___x_2071_ = lean_uint64_mix_hash(v___x_2069_, v___x_2070_);
v___x_2072_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3);
v___x_2073_ = lean_string_append(v___x_2072_, v___x_2068_);
lean_dec_ref(v___x_2068_);
v___x_2074_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_2075_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5);
v___x_2076_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2076_, 0, v___x_2073_);
lean_ctor_set(v___x_2076_, 1, v___x_2074_);
lean_ctor_set(v___x_2076_, 2, v___x_2075_);
lean_ctor_set_uint64(v___x_2076_, sizeof(void*)*3, v___x_2071_);
v___x_2077_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2067_);
lean_ctor_set(v___x_2077_, 1, v_ws_2044_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
lean_ctor_set(v___x_2077_, 3, v___x_2066_);
lean_ctor_set(v___x_2077_, 4, v_jobs_2046_);
lean_ctor_set(v___x_2077_, 5, v_val_2061_);
lean_ctor_set(v___x_2077_, 6, v_cancelTk_x3f_2047_);
return v___x_2077_;
}
v___jp_2078_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_box(0);
v___y_2050_ = v___y_2079_;
v___y_2051_ = v___y_2080_;
v___y_2052_ = v___y_2081_;
v___y_2053_ = v___y_2083_;
v___y_2054_ = v___y_2082_;
v___y_2055_ = v___y_2085_;
v___y_2056_ = v___y_2084_;
v___y_2057_ = v___y_2086_;
v___y_2058_ = v___y_2087_;
v___y_2059_ = v___y_2089_;
v___y_2060_ = v___y_2088_;
v_val_2061_ = v___x_2090_;
goto v___jp_2049_;
}
v___jp_2091_:
{
lean_object* v_outputsFile_x3f_2093_; 
v_outputsFile_x3f_2093_ = lean_ctor_get(v_cfg_2045_, 1);
lean_inc(v_outputsFile_x3f_2093_);
if (lean_obj_tag(v_outputsFile_x3f_2093_) == 0)
{
lean_object* v_toLogConfig_2094_; uint8_t v_oldMode_2095_; uint8_t v_trustHash_2096_; uint8_t v_noBuild_2097_; uint8_t v_failFast_2098_; uint8_t v_verbosity_2099_; uint8_t v_showSuccess_2100_; lean_object* v_outputsIdx_2101_; lean_object* v_leanOptOverrides_2102_; 
v_toLogConfig_2094_ = lean_ctor_get(v_cfg_2045_, 0);
lean_inc_ref(v_toLogConfig_2094_);
v_oldMode_2095_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5);
v_trustHash_2096_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 1);
v_noBuild_2097_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 2);
v_failFast_2098_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 3);
v_verbosity_2099_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 4);
v_showSuccess_2100_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 5);
v_outputsIdx_2101_ = lean_ctor_get(v_cfg_2045_, 2);
lean_inc(v_outputsIdx_2101_);
v_leanOptOverrides_2102_ = lean_ctor_get(v_cfg_2045_, 3);
lean_inc(v_leanOptOverrides_2102_);
lean_dec_ref(v_cfg_2045_);
v___y_2079_ = v_toLogConfig_2094_;
v___y_2080_ = v_oldMode_2095_;
v___y_2081_ = v_trustHash_2096_;
v___y_2082_ = v_showSuccess_2100_;
v___y_2083_ = v_leanOptOverrides_2102_;
v___y_2084_ = v_failFast_2098_;
v___y_2085_ = v_outputsIdx_2101_;
v___y_2086_ = v_val_2092_;
v___y_2087_ = v_verbosity_2099_;
v___y_2088_ = v_noBuild_2097_;
v___y_2089_ = v_outputsFile_x3f_2093_;
goto v___jp_2078_;
}
else
{
lean_object* v_toLogConfig_2103_; uint8_t v_oldMode_2104_; uint8_t v_trustHash_2105_; uint8_t v_noBuild_2106_; uint8_t v_failFast_2107_; uint8_t v_verbosity_2108_; uint8_t v_showSuccess_2109_; lean_object* v_outputsIdx_2110_; lean_object* v_leanOptOverrides_2111_; lean_object* v_packages_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_toLogConfig_2103_ = lean_ctor_get(v_cfg_2045_, 0);
lean_inc_ref(v_toLogConfig_2103_);
v_oldMode_2104_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5);
v_trustHash_2105_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 1);
v_noBuild_2106_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 2);
v_failFast_2107_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 3);
v_verbosity_2108_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 4);
v_showSuccess_2109_ = lean_ctor_get_uint8(v_cfg_2045_, sizeof(void*)*5 + 5);
v_outputsIdx_2110_ = lean_ctor_get(v_cfg_2045_, 2);
lean_inc(v_outputsIdx_2110_);
v_leanOptOverrides_2111_ = lean_ctor_get(v_cfg_2045_, 3);
lean_inc(v_leanOptOverrides_2111_);
lean_dec_ref(v_cfg_2045_);
v_packages_2112_ = lean_ctor_get(v_ws_2044_, 4);
v___x_2113_ = lean_array_get_size(v_packages_2112_);
v___x_2114_ = lean_nat_dec_lt(v_outputsIdx_2110_, v___x_2113_);
if (v___x_2114_ == 0)
{
v___y_2079_ = v_toLogConfig_2103_;
v___y_2080_ = v_oldMode_2104_;
v___y_2081_ = v_trustHash_2105_;
v___y_2082_ = v_showSuccess_2109_;
v___y_2083_ = v_leanOptOverrides_2111_;
v___y_2084_ = v_failFast_2107_;
v___y_2085_ = v_outputsIdx_2110_;
v___y_2086_ = v_val_2092_;
v___y_2087_ = v_verbosity_2108_;
v___y_2088_ = v_noBuild_2106_;
v___y_2089_ = v_outputsFile_x3f_2093_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7);
v___x_2116_ = lean_st_mk_ref(v___x_2115_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___y_2050_ = v_toLogConfig_2103_;
v___y_2051_ = v_oldMode_2104_;
v___y_2052_ = v_trustHash_2105_;
v___y_2053_ = v_leanOptOverrides_2111_;
v___y_2054_ = v_showSuccess_2109_;
v___y_2055_ = v_outputsIdx_2110_;
v___y_2056_ = v_failFast_2107_;
v___y_2057_ = v_val_2092_;
v___y_2058_ = v_verbosity_2108_;
v___y_2059_ = v_outputsFile_x3f_2093_;
v___y_2060_ = v_noBuild_2106_;
v_val_2061_ = v___x_2117_;
goto v___jp_2049_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_mkBuildContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2044_ = stack[0].m_obj;
lean_object* v_cfg_2045_ = stack[1].m_obj;
lean_object* v_jobs_2046_ = stack[2].m_obj;
lean_object* v_cancelTk_x3f_2047_ = stack[3].m_obj;
lean_object* v_res_2128_;
v_res_2128_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2044_, v_cfg_2045_, v_jobs_2046_, v_cancelTk_x3f_2047_);
stack->m_obj
 = v_res_2128_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object* v_ws_2129_, lean_object* v_cfg_2130_, lean_object* v_jobs_2131_, lean_object* v_cancelTk_x3f_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2129_, v_cfg_2130_, v_jobs_2131_, v_cancelTk_x3f_2132_);
return v_res_2134_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_log_2143_; uint8_t v_action_2144_; uint8_t v_wantsRebuild_2145_; uint8_t v_canceled_2146_; lean_object* v_trace_2147_; lean_object* v_buildTime_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2177_; 
v_log_2143_ = lean_ctor_get(v___y_2141_, 0);
v_action_2144_ = lean_ctor_get_uint8(v___y_2141_, sizeof(void*)*3);
v_wantsRebuild_2145_ = lean_ctor_get_uint8(v___y_2141_, sizeof(void*)*3 + 1);
v_canceled_2146_ = lean_ctor_get_uint8(v___y_2141_, sizeof(void*)*3 + 2);
v_trace_2147_ = lean_ctor_get(v___y_2141_, 1);
v_buildTime_2148_ = lean_ctor_get(v___y_2141_, 2);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___y_2141_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2150_ = v___y_2141_;
v_isShared_2151_ = v_isSharedCheck_2177_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_buildTime_2148_);
lean_inc(v_trace_2147_);
lean_inc(v_log_2143_);
lean_dec(v___y_2141_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2177_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_apply_7(v_build_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v_log_2143_, lean_box(0));
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2164_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_a_2154_ = lean_ctor_get(v___x_2152_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2156_ = v___x_2152_;
v_isShared_2157_ = v_isSharedCheck_2164_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2164_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v_a_2154_);
v___x_2159_ = v___x_2150_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2154_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_trace_2147_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_buildTime_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*3, v_action_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*3 + 1, v_wantsRebuild_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*3 + 2, v_canceled_2146_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2159_);
v___x_2161_ = v___x_2156_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2153_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2176_; 
v_a_2165_ = lean_ctor_get(v___x_2152_, 0);
v_a_2166_ = lean_ctor_get(v___x_2152_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2168_ = v___x_2152_;
v_isShared_2169_ = v_isSharedCheck_2176_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_inc(v_a_2165_);
lean_dec(v___x_2152_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2176_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v_a_2166_);
v___x_2171_ = v___x_2150_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2166_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_trace_2147_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_buildTime_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*3, v_action_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*3 + 1, v_wantsRebuild_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*3 + 2, v_canceled_2146_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2171_);
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2165_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_build_2135_ = stack[0].m_obj;
lean_object* v___y_2136_ = stack[1].m_obj;
lean_object* v___y_2137_ = stack[2].m_obj;
lean_object* v___y_2138_ = stack[3].m_obj;
lean_object* v___y_2139_ = stack[4].m_obj;
lean_object* v___y_2140_ = stack[5].m_obj;
lean_object* v___y_2141_ = stack[6].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v_res_2187_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_2189_, lean_object* v_build_2190_, lean_object* v_caption_2191_){
_start:
{
lean_object* v___f_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___f_2193_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2193_, 0, v_build_2190_);
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_box(1);
v___x_2198_ = lean_box(0);
v___x_2199_ = lean_st_mk_ref(v___x_2197_);
v___x_2200_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_2201_ = l_Lake_Job_async___redArg(v___x_2194_, v___f_2193_, v___x_2195_, v_caption_2191_, v___x_2200_, v___x_2198_, v___x_2196_, v___x_2199_, v_bctx_2189_);
v___x_2202_ = lean_st_ref_get(v___x_2199_);
lean_dec(v___x_2199_);
lean_dec(v___x_2202_);
return v___x_2201_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bctx_2189_ = stack[0].m_obj;
lean_object* v_build_2190_ = stack[1].m_obj;
lean_object* v_caption_2191_ = stack[2].m_obj;
lean_object* v_res_2203_;
v_res_2203_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2189_, v_build_2190_, v_caption_2191_);
stack->m_obj
 = v_res_2203_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_2204_, lean_object* v_build_2205_, lean_object* v_caption_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2204_, v_build_2205_, v_caption_2206_);
lean_dec_ref(v_bctx_2204_);
return v_res_2208_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_2209_, lean_object* v_bctx_2210_, lean_object* v_build_2211_, lean_object* v_caption_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2210_, v_build_2211_, v_caption_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_Workspace_startBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_bctx_2210_ = stack[1].m_obj;
lean_object* v_build_2211_ = stack[2].m_obj;
lean_object* v_caption_2212_ = stack[3].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_box(0), v_bctx_2210_, v_build_2211_, v_caption_2212_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_bctx_2217_, lean_object* v_build_2218_, lean_object* v_caption_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_2216_, v_bctx_2217_, v_build_2218_, v_caption_2219_);
lean_dec_ref(v_bctx_2217_);
return v_res_2221_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_2222_, uint8_t v___x_2223_, uint8_t v___x_2224_, lean_object* v_as_2225_, size_t v_i_2226_, size_t v_stop_2227_, lean_object* v_b_2228_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_usize_dec_eq(v_i_2226_, v_stop_2227_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; 
v___x_2231_ = lean_array_uget_borrowed(v_as_2225_, v_i_2226_);
lean_inc_ref(v___x_2222_);
v___x_2232_ = l_Lake_logToStream(v___x_2231_, v___x_2222_, v___x_2223_, v___x_2224_);
v___x_2233_ = ((size_t)1ULL);
v___x_2234_ = lean_usize_add(v_i_2226_, v___x_2233_);
v_i_2226_ = v___x_2234_;
v_b_2228_ = v___x_2232_;
goto _start;
}
else
{
lean_dec_ref(v___x_2222_);
return v_b_2228_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2222_ = stack[0].m_obj;
uint8_t v___x_2223_ = stack[1].m_num;
uint8_t v___x_2224_ = stack[2].m_num;
lean_object* v_as_2225_ = stack[3].m_obj;
size_t v_i_2226_ = stack[4].m_num;
size_t v_stop_2227_ = stack[5].m_num;
lean_object* v_b_2228_ = stack[6].m_obj;
lean_object* v_res_2236_;
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2222_, v___x_2223_, v___x_2224_, v_as_2225_, v_i_2226_, v_stop_2227_, v_b_2228_);
stack->m_obj
 = v_res_2236_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_2237_, lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v_as_2240_, lean_object* v_i_2241_, lean_object* v_stop_2242_, lean_object* v_b_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v___x_1088__boxed_2245_; uint8_t v___x_1089__boxed_2246_; size_t v_i_boxed_2247_; size_t v_stop_boxed_2248_; lean_object* v_res_2249_; 
v___x_1088__boxed_2245_ = lean_unbox(v___x_2238_);
v___x_1089__boxed_2246_ = lean_unbox(v___x_2239_);
v_i_boxed_2247_ = lean_unbox_usize(v_i_2241_);
lean_dec(v_i_2241_);
v_stop_boxed_2248_ = lean_unbox_usize(v_stop_2242_);
lean_dec(v_stop_2242_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2237_, v___x_1088__boxed_2245_, v___x_1089__boxed_2246_, v_as_2240_, v_i_boxed_2247_, v_stop_boxed_2248_, v_b_2243_);
lean_dec_ref(v_as_2240_);
return v_res_2249_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v___x_2250_, lean_object* v___x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_){
_start:
{
if (lean_obj_tag(v_x_2252_) == 0)
{
if (lean_obj_tag(v_x_2253_) == 0)
{
uint8_t v___x_2254_; 
v___x_2254_ = 1;
return v___x_2254_;
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = 0;
return v___x_2255_;
}
}
else
{
if (lean_obj_tag(v_x_2253_) == 0)
{
uint8_t v___x_2256_; 
v___x_2256_ = 0;
return v___x_2256_;
}
else
{
lean_object* v_val_2257_; uint8_t v___x_2258_; 
v_val_2257_ = lean_ctor_get(v_x_2253_, 0);
v___x_2258_ = lean_unbox(v_val_2257_);
if (v___x_2258_ == 0)
{
lean_object* v_val_2259_; uint8_t v___x_2260_; 
v_val_2259_ = lean_ctor_get(v_x_2252_, 0);
v___x_2260_ = lean_unbox(v_val_2259_);
if (v___x_2260_ == 0)
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_nat_dec_lt(v___x_2250_, v___x_2251_);
return v___x_2261_;
}
else
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_unbox(v_val_2257_);
return v___x_2262_;
}
}
else
{
lean_object* v_val_2263_; uint8_t v___x_2264_; 
v_val_2263_ = lean_ctor_get(v_x_2252_, 0);
v___x_2264_ = lean_unbox(v_val_2263_);
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2250_ = stack[0].m_obj;
lean_object* v___x_2251_ = stack[1].m_obj;
lean_object* v_x_2252_ = stack[2].m_obj;
lean_object* v_x_2253_ = stack[3].m_obj;
uint8_t v_res_2265_;
v_res_2265_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_2250_, v___x_2251_, v_x_2252_, v_x_2253_);
stack->m_num = v_res_2265_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v___x_2266_, lean_object* v___x_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
uint8_t v_res_2270_; lean_object* v_r_2271_; 
v_res_2270_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_2266_, v___x_2267_, v_x_2268_, v_x_2269_);
lean_dec(v_x_2269_);
lean_dec(v_x_2268_);
lean_dec(v___x_2267_);
lean_dec(v___x_2266_);
v_r_2271_ = lean_box(v_res_2270_);
return v_r_2271_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_2272_, uint8_t v___x_2273_, uint8_t v___x_2274_, lean_object* v_bctx_2275_, lean_object* v_out_2276_, lean_object* v_outputsFile_2277_){
_start:
{
lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2291_; lean_object* v___y_2292_; uint8_t v___y_2293_; lean_object* v_outputsRef_x3f_2305_; 
v_outputsRef_x3f_2305_ = lean_ctor_get(v_bctx_2275_, 5);
lean_inc(v_outputsRef_x3f_2305_);
if (lean_obj_tag(v_outputsRef_x3f_2305_) == 1)
{
lean_object* v_toContext_2306_; lean_object* v_toBuildConfig_2307_; lean_object* v_val_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2425_; 
v_toContext_2306_ = lean_ctor_get(v_bctx_2275_, 1);
lean_inc(v_toContext_2306_);
v_toBuildConfig_2307_ = lean_ctor_get(v_bctx_2275_, 0);
lean_inc_ref(v_toBuildConfig_2307_);
lean_dec_ref(v_bctx_2275_);
v_val_2308_ = lean_ctor_get(v_outputsRef_x3f_2305_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_outputsRef_x3f_2305_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2310_ = v_outputsRef_x3f_2305_;
v_isShared_2311_ = v_isSharedCheck_2425_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_val_2308_);
lean_dec(v_outputsRef_x3f_2305_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2425_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_lakeEnv_2312_; lean_object* v_packages_2313_; uint8_t v_verbosity_2314_; lean_object* v_outputsIdx_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_lakeEnv_2312_ = lean_ctor_get(v_toContext_2306_, 0);
lean_inc_ref(v_lakeEnv_2312_);
v_packages_2313_ = lean_ctor_get(v_toContext_2306_, 4);
lean_inc_ref(v_packages_2313_);
lean_dec(v_toContext_2306_);
v_verbosity_2314_ = lean_ctor_get_uint8(v_toBuildConfig_2307_, sizeof(void*)*5 + 4);
v_outputsIdx_2315_ = lean_ctor_get(v_toBuildConfig_2307_, 2);
lean_inc(v_outputsIdx_2315_);
lean_dec_ref(v_toBuildConfig_2307_);
v___x_2316_ = lean_array_get_size(v_packages_2313_);
v___x_2317_ = lean_nat_dec_lt(v_outputsIdx_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_object* v_putStr_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec(v_outputsIdx_2315_);
lean_dec_ref(v_packages_2313_);
lean_dec_ref(v_lakeEnv_2312_);
lean_del_object(v___x_2310_);
lean_dec(v_val_2308_);
lean_dec_ref(v_outputsFile_2277_);
lean_dec_ref(v___x_2272_);
v_putStr_2318_ = lean_ctor_get(v_out_2276_, 4);
lean_inc_ref(v_putStr_2318_);
lean_dec_ref(v_out_2276_);
v___x_2319_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_2320_ = lean_apply_2(v_putStr_2318_, v___x_2319_, lean_box(0));
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec_ref_known(v___x_2320_, 1);
goto v___jp_2301_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2323_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2324_ = lean_unsigned_to_nat(82u);
v___x_2325_ = lean_unsigned_to_nat(4u);
v___x_2326_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2327_ = lean_io_error_to_string(v_a_2321_);
v___x_2328_ = lean_string_append(v___x_2326_, v___x_2327_);
lean_dec_ref(v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v___x_2333_ = l_mkPanicMessageWithDecl(v___x_2322_, v___x_2323_, v___x_2324_, v___x_2325_, v___x_2332_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2333_);
goto v___jp_2301_;
}
}
else
{
lean_object* v___x_2335_; uint8_t v___y_2337_; uint8_t v___y_2401_; uint8_t v___y_2410_; lean_object* v_config_2411_; lean_object* v_enableArtifactCache_x3f_2412_; 
v___x_2335_ = lean_array_fget(v_packages_2313_, v_outputsIdx_2315_);
v_config_2411_ = lean_ctor_get(v___x_2335_, 6);
v_enableArtifactCache_x3f_2412_ = lean_ctor_get(v_config_2411_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_2412_) == 0)
{
lean_object* v_enableArtifactCache_x3f_2413_; 
v_enableArtifactCache_x3f_2413_ = lean_ctor_get(v_lakeEnv_2312_, 6);
lean_inc(v_enableArtifactCache_x3f_2413_);
lean_dec_ref(v_lakeEnv_2312_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_config_2416_; lean_object* v_enableArtifactCache_x3f_2417_; 
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_array_fget(v_packages_2313_, v___x_2414_);
lean_dec_ref(v_packages_2313_);
v_config_2416_ = lean_ctor_get(v___x_2415_, 6);
lean_inc_ref(v_config_2416_);
lean_dec(v___x_2415_);
v_enableArtifactCache_x3f_2417_ = lean_ctor_get(v_config_2416_, 24);
lean_inc(v_enableArtifactCache_x3f_2417_);
lean_dec_ref(v_config_2416_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2417_) == 0)
{
uint8_t v___x_2418_; 
v___x_2418_ = 0;
v___y_2401_ = v___x_2418_;
goto v___jp_2400_;
}
else
{
lean_object* v_val_2419_; uint8_t v___x_2420_; 
v_val_2419_ = lean_ctor_get(v_enableArtifactCache_x3f_2417_, 0);
lean_inc(v_val_2419_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2417_, 1);
v___x_2420_ = lean_unbox(v_val_2419_);
lean_dec(v_val_2419_);
v___y_2410_ = v___x_2420_;
goto v___jp_2409_;
}
}
else
{
lean_object* v_val_2421_; uint8_t v___x_2422_; 
lean_dec_ref(v_packages_2313_);
v_val_2421_ = lean_ctor_get(v_enableArtifactCache_x3f_2413_, 0);
lean_inc(v_val_2421_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2413_, 1);
v___x_2422_ = lean_unbox(v_val_2421_);
lean_dec(v_val_2421_);
v___y_2410_ = v___x_2422_;
goto v___jp_2409_;
}
}
else
{
lean_object* v_val_2423_; uint8_t v___x_2424_; 
lean_dec_ref(v_packages_2313_);
lean_dec_ref(v_lakeEnv_2312_);
v_val_2423_ = lean_ctor_get(v_enableArtifactCache_x3f_2412_, 0);
v___x_2424_ = lean_unbox(v_val_2423_);
v___y_2410_ = v___x_2424_;
goto v___jp_2409_;
}
v___jp_2336_:
{
lean_object* v___x_2338_; lean_object* v_config_2339_; lean_object* v_toLeanConfig_2340_; lean_object* v_platformIndependent_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2338_ = lean_st_ref_get(v_val_2308_);
lean_dec(v_val_2308_);
v_config_2339_ = lean_ctor_get(v___x_2335_, 6);
lean_inc_ref(v_config_2339_);
lean_dec(v___x_2335_);
v_toLeanConfig_2340_ = lean_ctor_get(v_config_2339_, 1);
lean_inc_ref(v_toLeanConfig_2340_);
lean_dec_ref(v_config_2339_);
v_platformIndependent_2341_ = lean_ctor_get(v_toLeanConfig_2340_, 10);
lean_inc(v_platformIndependent_2341_);
lean_dec_ref(v_toLeanConfig_2340_);
v___x_2342_ = lean_box(v___x_2317_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2342_);
v___x_2344_ = v___x_2310_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2345_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_outputsIdx_2315_, v___x_2316_, v_platformIndependent_2341_, v___x_2344_);
lean_dec_ref(v___x_2344_);
lean_dec(v_platformIndependent_2341_);
lean_dec(v_outputsIdx_2315_);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_2348_ = l_Lake_CacheMap_writeFile(v_outputsFile_2277_, v___x_2338_, v___x_2345_, v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 1);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 2);
v___x_2350_ = lean_array_get_size(v_a_2349_);
v___x_2351_ = lean_nat_dec_eq(v___x_2350_, v___x_2346_);
if (v___x_2351_ == 0)
{
if (v___y_2337_ == 0)
{
lean_dec(v_a_2349_);
lean_dec_ref(v_out_2276_);
lean_dec_ref(v___x_2272_);
goto v___jp_2279_;
}
else
{
lean_object* v_putStr_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_putStr_2352_ = lean_ctor_get(v_out_2276_, 4);
lean_inc_ref(v_putStr_2352_);
lean_dec_ref(v_out_2276_);
v___x_2353_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_2354_ = lean_apply_2(v_putStr_2352_, v___x_2353_, lean_box(0));
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_dec_ref_known(v___x_2354_, 1);
v___y_2282_ = v___x_2346_;
v___y_2283_ = v_a_2349_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2357_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2358_ = lean_unsigned_to_nat(82u);
v___x_2359_ = lean_unsigned_to_nat(4u);
v___x_2360_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2361_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2361_, v___y_2337_);
v___x_2363_ = lean_string_append(v___x_2360_, v___x_2362_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2365_ = lean_string_append(v___x_2363_, v___x_2364_);
v___x_2366_ = lean_io_error_to_string(v_a_2355_);
v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
lean_dec_ref(v___x_2366_);
v___x_2368_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2369_ = lean_string_append(v___x_2367_, v___x_2368_);
v___x_2370_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_2371_ = lean_string_append(v___x_2369_, v___x_2370_);
v___x_2372_ = l_mkPanicMessageWithDecl(v___x_2356_, v___x_2357_, v___x_2358_, v___x_2359_, v___x_2371_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2372_);
v___y_2282_ = v___x_2346_;
v___y_2283_ = v_a_2349_;
goto v___jp_2281_;
}
}
}
else
{
lean_dec(v_a_2349_);
lean_dec_ref(v_out_2276_);
lean_dec_ref(v___x_2272_);
goto v___jp_2279_;
}
}
else
{
lean_object* v_a_2374_; lean_object* v_putStr_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2374_ = lean_ctor_get(v___x_2348_, 1);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2348_, 2);
v_putStr_2375_ = lean_ctor_get(v_out_2276_, 4);
lean_inc_ref(v_putStr_2375_);
lean_dec_ref(v_out_2276_);
v___x_2376_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_2377_ = lean_apply_2(v_putStr_2375_, v___x_2376_, lean_box(0));
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_dec_ref_known(v___x_2377_, 1);
v___y_2291_ = v___x_2346_;
v___y_2292_ = v_a_2374_;
v___y_2293_ = v___y_2337_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2380_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2381_ = lean_unsigned_to_nat(82u);
v___x_2382_ = lean_unsigned_to_nat(4u);
v___x_2383_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2384_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2384_, v___x_2317_);
v___x_2386_ = lean_string_append(v___x_2383_, v___x_2385_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2388_ = lean_string_append(v___x_2386_, v___x_2387_);
v___x_2389_ = lean_io_error_to_string(v_a_2378_);
v___x_2390_ = lean_string_append(v___x_2388_, v___x_2389_);
lean_dec_ref(v___x_2389_);
v___x_2391_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2392_ = lean_string_append(v___x_2390_, v___x_2391_);
v___x_2393_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_2394_ = lean_string_append(v___x_2392_, v___x_2393_);
v___x_2395_ = l_mkPanicMessageWithDecl(v___x_2379_, v___x_2380_, v___x_2381_, v___x_2382_, v___x_2394_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2395_);
v___y_2291_ = v___x_2346_;
v___y_2292_ = v_a_2374_;
v___y_2293_ = v___y_2337_;
goto v___jp_2290_;
}
}
}
}
v___jp_2398_:
{
if (v_verbosity_2314_ == 2)
{
v___y_2337_ = v___x_2317_;
goto v___jp_2336_;
}
else
{
uint8_t v___x_2399_; 
v___x_2399_ = 0;
v___y_2337_ = v___x_2399_;
goto v___jp_2336_;
}
}
v___jp_2400_:
{
lean_object* v_baseName_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_baseName_2402_ = lean_ctor_get(v___x_2335_, 1);
lean_inc(v_baseName_2402_);
v___x_2403_ = l_Lean_Name_toString(v_baseName_2402_, v___y_2401_);
v___x_2404_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_2405_ = lean_string_append(v___x_2403_, v___x_2404_);
v___x_2406_ = 2;
v___x_2407_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*1, v___x_2406_);
lean_inc_ref(v___x_2272_);
v___x_2408_ = l_Lake_logToStream(v___x_2407_, v___x_2272_, v___x_2273_, v___x_2274_);
lean_dec_ref_known(v___x_2407_, 1);
goto v___jp_2398_;
}
v___jp_2409_:
{
if (v___y_2410_ == 0)
{
v___y_2401_ = v___y_2410_;
goto v___jp_2400_;
}
else
{
goto v___jp_2398_;
}
}
}
}
}
else
{
lean_object* v_putStr_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec(v_outputsRef_x3f_2305_);
lean_dec_ref(v_outputsFile_2277_);
lean_dec_ref(v_bctx_2275_);
lean_dec_ref(v___x_2272_);
v_putStr_2426_ = lean_ctor_get(v_out_2276_, 4);
lean_inc_ref(v_putStr_2426_);
lean_dec_ref(v_out_2276_);
v___x_2427_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_2428_ = lean_apply_2(v_putStr_2426_, v___x_2427_, lean_box(0));
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_dec_ref_known(v___x_2428_, 1);
goto v___jp_2303_;
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2432_ = lean_unsigned_to_nat(82u);
v___x_2433_ = lean_unsigned_to_nat(4u);
v___x_2434_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2435_ = lean_io_error_to_string(v_a_2429_);
v___x_2436_ = lean_string_append(v___x_2434_, v___x_2435_);
lean_dec_ref(v___x_2435_);
v___x_2437_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2438_ = lean_string_append(v___x_2436_, v___x_2437_);
v___x_2439_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_2440_ = lean_string_append(v___x_2438_, v___x_2439_);
v___x_2441_ = l_mkPanicMessageWithDecl(v___x_2430_, v___x_2431_, v___x_2432_, v___x_2433_, v___x_2440_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2441_);
goto v___jp_2303_;
}
}
v___jp_2279_:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_box(0);
return v___x_2280_;
}
v___jp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2284_ = lean_array_get_size(v___y_2283_);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_nat_dec_lt(v___y_2282_, v___x_2284_);
if (v___x_2286_ == 0)
{
lean_dec_ref(v___y_2283_);
lean_dec_ref(v___x_2272_);
return v___x_2285_;
}
else
{
size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = ((size_t)0ULL);
v___x_2288_ = lean_usize_of_nat(v___x_2284_);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2272_, v___x_2273_, v___x_2274_, v___y_2283_, v___x_2287_, v___x_2288_, v___x_2285_);
lean_dec_ref(v___y_2283_);
return v___x_2289_;
}
}
v___jp_2290_:
{
if (v___y_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___x_2272_);
v___x_2294_ = lean_box(0);
return v___x_2294_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2295_ = lean_array_get_size(v___y_2292_);
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_nat_dec_lt(v___y_2291_, v___x_2295_);
if (v___x_2297_ == 0)
{
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___x_2272_);
return v___x_2296_;
}
else
{
size_t v___x_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = ((size_t)0ULL);
v___x_2299_ = lean_usize_of_nat(v___x_2295_);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2272_, v___x_2273_, v___x_2274_, v___y_2292_, v___x_2298_, v___x_2299_, v___x_2296_);
lean_dec_ref(v___y_2292_);
return v___x_2300_;
}
}
}
v___jp_2301_:
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_box(0);
return v___x_2302_;
}
v___jp_2303_:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_box(0);
return v___x_2304_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2272_ = stack[0].m_obj;
uint8_t v___x_2273_ = stack[1].m_num;
uint8_t v___x_2274_ = stack[2].m_num;
lean_object* v_bctx_2275_ = stack[3].m_obj;
lean_object* v_out_2276_ = stack[4].m_obj;
lean_object* v_outputsFile_2277_ = stack[5].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2272_, v___x_2273_, v___x_2274_, v_bctx_2275_, v_out_2276_, v_outputsFile_2277_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2444_, lean_object* v___x_2445_, lean_object* v___x_2446_, lean_object* v_bctx_2447_, lean_object* v_out_2448_, lean_object* v_outputsFile_2449_, lean_object* v_a_2450_){
_start:
{
uint8_t v___x_1365__boxed_2451_; uint8_t v___x_1366__boxed_2452_; lean_object* v_res_2453_; 
v___x_1365__boxed_2451_ = lean_unbox(v___x_2445_);
v___x_1366__boxed_2452_ = lean_unbox(v___x_2446_);
v_res_2453_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2444_, v___x_1365__boxed_2451_, v___x_1366__boxed_2452_, v_bctx_2447_, v_out_2448_, v_outputsFile_2449_);
return v_res_2453_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2454_, lean_object* v_bctx_2455_, lean_object* v_mctx_2456_, lean_object* v_result_2457_){
_start:
{
lean_object* v___y_2460_; lean_object* v_out_2463_; uint8_t v_outLv_2464_; uint8_t v_useAnsi_2465_; lean_object* v_toMonitorResult_2466_; lean_object* v_out_2467_; lean_object* v___x_2483_; lean_object* v_outputsFile_x3f_2484_; 
v_out_2463_ = lean_ctor_get(v_mctx_2456_, 1);
lean_inc_ref_n(v_out_2463_, 2);
v_outLv_2464_ = lean_ctor_get_uint8(v_mctx_2456_, sizeof(void*)*4);
v_useAnsi_2465_ = lean_ctor_get_uint8(v_mctx_2456_, sizeof(void*)*4 + 4);
lean_dec_ref(v_mctx_2456_);
v_toMonitorResult_2466_ = lean_ctor_get(v_result_2457_, 0);
lean_inc_ref_n(v_toMonitorResult_2466_, 2);
v_out_2467_ = lean_ctor_get(v_result_2457_, 1);
lean_inc_ref(v_out_2467_);
lean_dec_ref(v_result_2457_);
v___x_2483_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2454_, v_out_2463_, v_toMonitorResult_2466_);
v_outputsFile_x3f_2484_ = lean_ctor_get(v_cfg_2454_, 1);
if (lean_obj_tag(v_outputsFile_x3f_2484_) == 1)
{
lean_object* v_val_2485_; lean_object* v___x_2486_; 
v_val_2485_ = lean_ctor_get(v_outputsFile_x3f_2484_, 0);
lean_inc(v_val_2485_);
lean_inc_ref(v_out_2463_);
v___x_2486_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2463_, v_outLv_2464_, v_useAnsi_2465_, v_bctx_2455_, v_out_2463_, v_val_2485_);
goto v___jp_2468_;
}
else
{
lean_dec_ref(v_out_2463_);
lean_dec_ref(v_bctx_2455_);
goto v___jp_2468_;
}
v___jp_2459_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_mk_io_user_error(v___y_2460_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
v___jp_2468_:
{
if (lean_obj_tag(v_out_2467_) == 0)
{
uint8_t v_noBuild_2469_; 
v_noBuild_2469_ = lean_ctor_get_uint8(v_cfg_2454_, sizeof(void*)*5 + 2);
lean_dec_ref(v_cfg_2454_);
if (v_noBuild_2469_ == 0)
{
lean_object* v_a_2470_; 
lean_dec_ref(v_toMonitorResult_2466_);
v_a_2470_ = lean_ctor_get(v_out_2467_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v_out_2467_, 1);
v___y_2460_ = v_a_2470_;
goto v___jp_2459_;
}
else
{
uint8_t v_wantsRebuild_2471_; 
v_wantsRebuild_2471_ = lean_ctor_get_uint8(v_toMonitorResult_2466_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2466_);
if (v_wantsRebuild_2471_ == 0)
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v_out_2467_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v_out_2467_, 1);
v___y_2460_ = v_a_2472_;
goto v___jp_2459_;
}
else
{
uint8_t v___x_2473_; lean_object* v___x_2474_; 
lean_dec_ref_known(v_out_2467_, 1);
v___x_2473_ = 3;
v___x_2474_ = lean_io_exit(v___x_2473_);
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_toMonitorResult_2466_);
lean_dec_ref(v_cfg_2454_);
v_a_2475_ = lean_ctor_get(v_out_2467_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_out_2467_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v_out_2467_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v_out_2467_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 0);
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2454_ = stack[0].m_obj;
lean_object* v_bctx_2455_ = stack[1].m_obj;
lean_object* v_mctx_2456_ = stack[2].m_obj;
lean_object* v_result_2457_ = stack[3].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2454_, v_bctx_2455_, v_mctx_2456_, v_result_2457_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2488_, lean_object* v_bctx_2489_, lean_object* v_mctx_2490_, lean_object* v_result_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2488_, v_bctx_2489_, v_mctx_2490_, v_result_2491_);
return v_res_2493_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2494_, lean_object* v_cfg_2495_, lean_object* v_bctx_2496_, lean_object* v_mctx_2497_, lean_object* v_result_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2495_, v_bctx_2496_, v_mctx_2497_, v_result_2498_);
return v___x_2500_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_finalizeBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2495_ = stack[1].m_obj;
lean_object* v_bctx_2496_ = stack[2].m_obj;
lean_object* v_mctx_2497_ = stack[3].m_obj;
lean_object* v_result_2498_ = stack[4].m_obj;
lean_object* v_res_2501_;
v_res_2501_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_box(0), v_cfg_2495_, v_bctx_2496_, v_mctx_2497_, v_result_2498_);
stack->m_obj
 = v_res_2501_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2502_, lean_object* v_cfg_2503_, lean_object* v_bctx_2504_, lean_object* v_mctx_2505_, lean_object* v_result_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2502_, v_cfg_2503_, v_bctx_2504_, v_mctx_2505_, v_result_2506_);
return v_res_2508_;
}
}
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2509_, lean_object* v_build_2510_, lean_object* v_cfg_2511_, lean_object* v_caption_2512_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_cancelTk_x3f_2517_; uint8_t v_failFast_2523_; 
v___x_2514_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2515_ = lean_st_mk_ref(v___x_2514_);
v_failFast_2523_ = lean_ctor_get_uint8(v_cfg_2511_, sizeof(void*)*5 + 3);
if (v_failFast_2523_ == 0)
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_box(0);
v_cancelTk_x3f_2517_ = v___x_2524_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = l_IO_CancelToken_new();
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
v_cancelTk_x3f_2517_ = v___x_2526_;
goto v___jp_2516_;
}
v___jp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_inc(v_cancelTk_x3f_2517_);
lean_inc(v___x_2515_);
v___x_2518_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2511_, v___x_2515_, v_cancelTk_x3f_2517_);
lean_inc_ref(v_cfg_2511_);
v___x_2519_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2509_, v_cfg_2511_, v___x_2515_, v_cancelTk_x3f_2517_);
v___x_2520_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2519_, v_build_2510_, v_caption_2512_);
v___x_2521_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2518_, v___x_2520_);
v___x_2522_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2511_, v___x_2519_, v___x_2518_, v___x_2521_);
return v___x_2522_;
}
}
}
LEAN_EXPORT void l_Lake_Workspace_runFetchM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2509_ = stack[0].m_obj;
lean_object* v_build_2510_ = stack[1].m_obj;
lean_object* v_cfg_2511_ = stack[2].m_obj;
lean_object* v_caption_2512_ = stack[3].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2509_, v_build_2510_, v_cfg_2511_, v_caption_2512_);
stack->m_obj
 = v_res_2527_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2528_, lean_object* v_build_2529_, lean_object* v_cfg_2530_, lean_object* v_caption_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2528_, v_build_2529_, v_cfg_2530_, v_caption_2531_);
return v_res_2533_;
}
}
lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2534_, lean_object* v_ws_2535_, lean_object* v_build_2536_, lean_object* v_cfg_2537_, lean_object* v_caption_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2535_, v_build_2536_, v_cfg_2537_, v_caption_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT void l_Lake_Workspace_runFetchM_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2535_ = stack[1].m_obj;
lean_object* v_build_2536_ = stack[2].m_obj;
lean_object* v_cfg_2537_ = stack[3].m_obj;
lean_object* v_caption_2538_ = stack[4].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l_Lake_Workspace_runFetchM(lean_box(0), v_ws_2535_, v_build_2536_, v_cfg_2537_, v_caption_2538_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_ws_2543_, lean_object* v_build_2544_, lean_object* v_cfg_2545_, lean_object* v_caption_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2542_, v_ws_2543_, v_build_2544_, v_cfg_2545_, v_caption_2546_);
return v_res_2548_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2552_, lean_object* v_job_2553_){
_start:
{
lean_object* v___x_2555_; lean_object* v_out_2556_; 
v___x_2555_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2552_, v_job_2553_);
v_out_2556_ = lean_ctor_get(v___x_2555_, 1);
lean_inc_ref(v_out_2556_);
if (lean_obj_tag(v_out_2556_) == 0)
{
lean_object* v_toMonitorResult_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2572_; 
v_toMonitorResult_2557_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2555_, 1);
lean_dec(v_unused_2573_);
v___x_2559_ = v___x_2555_;
v_isShared_2560_ = v_isSharedCheck_2572_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_toMonitorResult_2557_);
lean_dec(v___x_2555_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2572_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2571_; 
v_a_2561_ = lean_ctor_get(v_out_2556_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_out_2556_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2563_ = v_out_2556_;
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v_out_2556_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2566_);
v___x_2568_ = v___x_2559_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_toMonitorResult_2557_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2597_; 
v_a_2574_ = lean_ctor_get(v_out_2556_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_out_2556_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2576_ = v_out_2556_;
v_isShared_2577_ = v_isSharedCheck_2597_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v_out_2556_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2597_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_toMonitorResult_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2595_; 
v_toMonitorResult_2578_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v___x_2555_, 1);
lean_dec(v_unused_2596_);
v___x_2580_ = v___x_2555_;
v_isShared_2581_ = v_isSharedCheck_2595_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_toMonitorResult_2578_);
lean_dec(v___x_2555_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2595_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_task_2582_; lean_object* v___x_2583_; 
v_task_2582_ = lean_ctor_get(v_a_2574_, 0);
lean_inc_ref(v_task_2582_);
lean_dec(v_a_2574_);
v___x_2583_ = lean_io_wait(v_task_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 2);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_a_2584_);
v___x_2586_ = v___x_2576_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v___x_2586_);
v___x_2588_ = v___x_2580_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_toMonitorResult_2578_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_dec_ref_known(v___x_2583_, 2);
lean_del_object(v___x_2576_);
v___x_2591_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v___x_2591_);
v___x_2593_ = v___x_2580_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_toMonitorResult_2578_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_2552_ = stack[0].m_obj;
lean_object* v_job_2553_ = stack[1].m_obj;
lean_object* v_res_2598_;
v_res_2598_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2552_, v_job_2553_);
stack->m_obj
 = v_res_2598_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2599_, lean_object* v_job_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2599_, v_job_2600_);
lean_dec_ref(v_mctx_2599_);
return v_res_2602_;
}
}
lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2603_, lean_object* v_mctx_2604_, lean_object* v_job_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2604_, v_job_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Run_0__Lake_monitorBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_2604_ = stack[1].m_obj;
lean_object* v_job_2605_ = stack[2].m_obj;
lean_object* v_res_2608_;
v_res_2608_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_box(0), v_mctx_2604_, v_job_2605_);
stack->m_obj
 = v_res_2608_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2609_, lean_object* v_mctx_2610_, lean_object* v_job_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2609_, v_mctx_2610_, v_job_2611_);
lean_dec_ref(v_mctx_2610_);
return v_res_2613_;
}
}
uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2628_, lean_object* v_build_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_out_2642_; 
v___x_2631_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2632_ = lean_st_mk_ref(v___x_2631_);
v___x_2633_ = 0;
v___x_2634_ = 1;
v___x_2635_ = lean_box(0);
v___x_2636_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2632_);
v___x_2637_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2636_, v___x_2632_, v___x_2635_);
v___x_2638_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2628_, v___x_2636_, v___x_2632_, v___x_2635_);
v___x_2639_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2640_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2638_, v_build_2629_, v___x_2639_);
lean_dec_ref(v___x_2638_);
v___x_2641_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2637_, v___x_2640_);
lean_dec_ref(v___x_2637_);
v_out_2642_ = lean_ctor_get(v___x_2641_, 1);
lean_inc_ref(v_out_2642_);
lean_dec_ref(v___x_2641_);
if (lean_obj_tag(v_out_2642_) == 0)
{
lean_dec_ref_known(v_out_2642_, 1);
return v___x_2633_;
}
else
{
lean_dec_ref_known(v_out_2642_, 1);
return v___x_2634_;
}
}
}
LEAN_EXPORT void l_Lake_Workspace_checkNoBuild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2628_ = stack[0].m_obj;
lean_object* v_build_2629_ = stack[1].m_obj;
uint8_t v_res_2643_;
v_res_2643_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2628_, v_build_2629_);
stack->m_num = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2644_, lean_object* v_build_2645_, lean_object* v_a_2646_){
_start:
{
uint8_t v_res_2647_; lean_object* v_r_2648_; 
v_res_2647_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2644_, v_build_2645_);
v_r_2648_ = lean_box(v_res_2647_);
return v_r_2648_;
}
}
uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2649_, lean_object* v_ws_2650_, lean_object* v_build_2651_){
_start:
{
uint8_t v___x_2653_; 
v___x_2653_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2650_, v_build_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT void l_Lake_Workspace_checkNoBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2650_ = stack[1].m_obj;
lean_object* v_build_2651_ = stack[2].m_obj;
uint8_t v_res_2654_;
v_res_2654_ = l_Lake_Workspace_checkNoBuild(lean_box(0), v_ws_2650_, v_build_2651_);
stack->m_num = v_res_2654_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2655_, lean_object* v_ws_2656_, lean_object* v_build_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2655_, v_ws_2656_, v_build_2657_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2661_, lean_object* v_build_2662_, lean_object* v_cfg_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v_cancelTk_x3f_2668_; uint8_t v_failFast_2675_; 
v___x_2665_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2666_ = lean_st_mk_ref(v___x_2665_);
v_failFast_2675_ = lean_ctor_get_uint8(v_cfg_2663_, sizeof(void*)*5 + 3);
if (v_failFast_2675_ == 0)
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_box(0);
v_cancelTk_x3f_2668_ = v___x_2676_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = l_IO_CancelToken_new();
v___x_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
v_cancelTk_x3f_2668_ = v___x_2678_;
goto v___jp_2667_;
}
v___jp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_inc(v_cancelTk_x3f_2668_);
lean_inc(v___x_2666_);
v___x_2669_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2663_, v___x_2666_, v_cancelTk_x3f_2668_);
lean_inc_ref(v_cfg_2663_);
v___x_2670_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2661_, v_cfg_2663_, v___x_2666_, v_cancelTk_x3f_2668_);
v___x_2671_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2672_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2670_, v_build_2662_, v___x_2671_);
v___x_2673_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2669_, v___x_2672_);
v___x_2674_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2663_, v___x_2670_, v___x_2669_, v___x_2673_);
return v___x_2674_;
}
}
}
LEAN_EXPORT void l_Lake_Workspace_runBuild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2661_ = stack[0].m_obj;
lean_object* v_build_2662_ = stack[1].m_obj;
lean_object* v_cfg_2663_ = stack[2].m_obj;
lean_object* v_res_2679_;
v_res_2679_ = l_Lake_Workspace_runBuild___redArg(v_ws_2661_, v_build_2662_, v_cfg_2663_);
stack->m_obj
 = v_res_2679_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2680_, lean_object* v_build_2681_, lean_object* v_cfg_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lake_Workspace_runBuild___redArg(v_ws_2680_, v_build_2681_, v_cfg_2682_);
return v_res_2684_;
}
}
lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2685_, lean_object* v_ws_2686_, lean_object* v_build_2687_, lean_object* v_cfg_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lake_Workspace_runBuild___redArg(v_ws_2686_, v_build_2687_, v_cfg_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT void l_Lake_Workspace_runBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_2686_ = stack[1].m_obj;
lean_object* v_build_2687_ = stack[2].m_obj;
lean_object* v_cfg_2688_ = stack[3].m_obj;
lean_object* v_res_2691_;
v_res_2691_ = l_Lake_Workspace_runBuild(lean_box(0), v_ws_2686_, v_build_2687_, v_cfg_2688_);
stack->m_obj
 = v_res_2691_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2692_, lean_object* v_ws_2693_, lean_object* v_build_2694_, lean_object* v_cfg_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lake_Workspace_runBuild(v_00_u03b1_2692_, v_ws_2693_, v_build_2694_, v_cfg_2695_);
return v_res_2697_;
}
}
lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2698_, lean_object* v_cfg_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; 
lean_inc(v_a_2700_);
v___x_2702_ = l_Lake_Workspace_runBuild___redArg(v_a_2700_, v_build_2698_, v_cfg_2699_);
return v___x_2702_;
}
}
LEAN_EXPORT void l_Lake_runBuild___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_build_2698_ = stack[0].m_obj;
lean_object* v_cfg_2699_ = stack[1].m_obj;
lean_object* v_a_2700_ = stack[2].m_obj;
lean_object* v_res_2703_;
v_res_2703_ = l_Lake_runBuild___redArg(v_build_2698_, v_cfg_2699_, v_a_2700_);
stack->m_obj
 = v_res_2703_;
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2704_, lean_object* v_cfg_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lake_runBuild___redArg(v_build_2704_, v_cfg_2705_, v_a_2706_);
lean_dec(v_a_2706_);
return v_res_2708_;
}
}
lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2709_, lean_object* v_build_2710_, lean_object* v_cfg_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; 
lean_inc(v_a_2712_);
v___x_2714_ = l_Lake_Workspace_runBuild___redArg(v_a_2712_, v_build_2710_, v_cfg_2711_);
return v___x_2714_;
}
}
LEAN_EXPORT void l_Lake_runBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_build_2710_ = stack[1].m_obj;
lean_object* v_cfg_2711_ = stack[2].m_obj;
lean_object* v_a_2712_ = stack[3].m_obj;
lean_object* v_res_2715_;
v_res_2715_ = l_Lake_runBuild(lean_box(0), v_build_2710_, v_cfg_2711_, v_a_2712_);
stack->m_obj
 = v_res_2715_;
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_build_2717_, lean_object* v_cfg_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lake_runBuild(v_00_u03b1_2716_, v_build_2717_, v_cfg_2718_, v_a_2719_);
lean_dec(v_a_2719_);
return v_res_2721_;
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
