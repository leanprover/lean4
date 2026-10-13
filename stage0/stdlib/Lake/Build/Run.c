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
uint8_t v___y_14248__boxed_423_; uint8_t v_useAnsi_14249__boxed_424_; size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v___y_14248__boxed_423_ = lean_unbox(v___y_415_);
v_useAnsi_14249__boxed_424_ = lean_unbox(v_useAnsi_416_);
v_i_boxed_425_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_414_, v___y_14248__boxed_423_, v_useAnsi_14249__boxed_424_, v_as_417_, v_i_boxed_425_, v_stop_boxed_426_, v_b_420_, v___y_421_);
lean_dec_ref(v_as_417_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___y_442_; lean_object* v_val_443_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_454_; lean_object* v_jobNo_457_; lean_object* v_totalJobs_458_; uint8_t v_wantsRebuild_459_; lean_object* v_failures_460_; lean_object* v_resetCtrl_461_; lean_object* v_lastUpdate_462_; lean_object* v_spinnerIdx_463_; lean_object* v_out_464_; uint8_t v_outLv_465_; uint8_t v_failLv_466_; uint8_t v_minAction_467_; uint8_t v_showOptional_468_; uint8_t v_useAnsi_469_; uint8_t v_showProgress_470_; uint8_t v_showTime_471_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; uint8_t v___y_478_; lean_object* v___y_486_; uint8_t v___y_487_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_495_; lean_object* v___y_496_; uint8_t v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; uint8_t v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; uint8_t v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v_task_570_; lean_object* v_caption_571_; uint8_t v_optional_572_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; uint8_t v___y_579_; uint8_t v___y_580_; uint8_t v___y_581_; lean_object* v___y_582_; uint8_t v___y_583_; uint32_t v___y_584_; uint8_t v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; uint8_t v___y_616_; uint8_t v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; uint8_t v___y_620_; uint32_t v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; uint8_t v___y_630_; uint8_t v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; uint8_t v___y_635_; uint32_t v___y_636_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; uint8_t v___y_652_; uint8_t v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; uint8_t v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; uint32_t v___y_659_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; uint8_t v___y_666_; uint8_t v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_679_; lean_object* v___y_680_; uint8_t v___y_681_; uint8_t v___y_682_; uint8_t v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; uint8_t v___y_689_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; uint8_t v___y_695_; uint8_t v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; uint8_t v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; uint8_t v___y_709_; uint8_t v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; lean_object* v___y_731_; uint8_t v___y_732_; uint8_t v___y_733_; lean_object* v___y_734_; uint8_t v___y_735_; lean_object* v___y_736_; uint8_t v___y_737_; uint8_t v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_759_; uint8_t v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; uint8_t v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; uint8_t v___y_766_; lean_object* v___y_767_; uint8_t v___y_768_; lean_object* v___y_783_; uint8_t v___y_784_; uint8_t v___y_785_; lean_object* v___y_786_; uint8_t v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; uint8_t v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v___y_796_; uint8_t v___y_797_; uint8_t v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_809_; lean_object* v___x_821_; lean_object* v_a_822_; 
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
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_val_443_);
lean_ctor_set(v___x_444_, 1, v___y_442_);
return v___x_444_;
}
v___jp_445_:
{
lean_object* v_out_448_; lean_object* v_flush_449_; lean_object* v___x_450_; 
v_out_448_ = lean_ctor_get(v___y_446_, 1);
v_flush_449_ = lean_ctor_get(v_out_448_, 0);
lean_inc_ref(v_flush_449_);
v___x_450_ = lean_apply_1(v_flush_449_, lean_box(0));
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___y_442_ = v___y_447_;
v_val_443_ = v_a_451_;
goto v___jp_441_;
}
else
{
lean_object* v___x_452_; 
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = lean_box(0);
v___y_442_ = v___y_447_;
v_val_443_ = v___x_452_;
goto v___jp_441_;
}
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___y_454_);
return v___x_456_;
}
v___jp_472_:
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_lt(v___y_473_, v___y_476_);
lean_dec(v___y_473_);
if (v___x_479_ == 0)
{
lean_dec(v___y_476_);
lean_dec_ref(v___y_474_);
v___y_446_ = v___y_475_;
v___y_447_ = v___y_477_;
goto v___jp_445_;
}
else
{
lean_object* v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v_snd_484_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___y_476_);
lean_dec(v___y_476_);
lean_inc_ref(v_out_464_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_464_, v___y_478_, v_useAnsi_469_, v___y_474_, v___x_481_, v___x_482_, v___x_480_, v___y_477_);
lean_dec_ref(v___y_474_);
v_snd_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_snd_484_);
lean_dec_ref(v___x_483_);
v___y_446_ = v___y_475_;
v___y_447_ = v_snd_484_;
goto v___jp_445_;
}
}
v___jp_485_:
{
if (v___y_488_ == 0)
{
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_486_);
v___y_446_ = v___y_489_;
v___y_447_ = v___y_492_;
goto v___jp_445_;
}
else
{
if (v___y_487_ == 0)
{
v___y_473_ = v___y_486_;
v___y_474_ = v___y_490_;
v___y_475_ = v___y_489_;
v___y_476_ = v___y_491_;
v___y_477_ = v___y_492_;
v___y_478_ = v_outLv_465_;
goto v___jp_472_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = 0;
v___y_473_ = v___y_486_;
v___y_474_ = v___y_490_;
v___y_475_ = v___y_489_;
v___y_476_ = v___y_491_;
v___y_477_ = v___y_492_;
v___y_478_ = v___x_493_;
goto v___jp_472_;
}
}
}
v___jp_494_:
{
lean_object* v_out_504_; lean_object* v_jobNo_505_; lean_object* v_totalJobs_506_; uint8_t v_wantsRebuild_507_; lean_object* v_failures_508_; lean_object* v_resetCtrl_509_; lean_object* v_lastUpdate_510_; lean_object* v_spinnerIdx_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_557_; 
v_out_504_ = lean_ctor_get(v___y_500_, 1);
v_jobNo_505_ = lean_ctor_get(v___y_496_, 0);
v_totalJobs_506_ = lean_ctor_get(v___y_496_, 1);
v_wantsRebuild_507_ = lean_ctor_get_uint8(v___y_496_, sizeof(void*)*6);
v_failures_508_ = lean_ctor_get(v___y_496_, 2);
v_resetCtrl_509_ = lean_ctor_get(v___y_496_, 3);
v_lastUpdate_510_ = lean_ctor_get(v___y_496_, 4);
v_spinnerIdx_511_ = lean_ctor_get(v___y_496_, 5);
v_isSharedCheck_557_ = !lean_is_exclusive(v___y_496_);
if (v_isSharedCheck_557_ == 0)
{
v___x_513_ = v___y_496_;
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
lean_dec(v___y_496_);
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
v___y_487_ = v___y_497_;
v___y_488_ = v___y_498_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_499_;
v___y_491_ = v___y_502_;
v___y_492_ = v___x_518_;
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
lean_inc(v___y_495_);
v___x_534_ = l_Lean_Name_num___override(v___x_533_, v___y_495_);
v___x_535_ = l_Lean_Name_str___override(v___x_534_, v___x_532_);
v___x_536_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_537_ = l_Lean_Name_str___override(v___x_535_, v___x_536_);
v___x_538_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_537_, v___y_501_);
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
lean_inc_n(v___y_495_, 2);
v___x_550_ = l_Std_Format_pretty(v___x_548_, v___x_549_, v___y_495_, v___y_495_);
v___x_551_ = lean_string_append(v___x_545_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_mkPanicMessageWithDecl(v___x_527_, v___x_528_, v___x_529_, v___x_530_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_552_);
v___y_486_ = v___y_495_;
v___y_487_ = v___y_497_;
v___y_488_ = v___y_498_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_499_;
v___y_491_ = v___y_502_;
v___y_492_ = v___x_518_;
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
v___x_569_ = l_Lake_Ansi_chalk(v___y_568_, v___y_562_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___y_568_);
v___y_495_ = v___y_560_;
v___y_496_ = v___y_559_;
v___y_497_ = v___y_561_;
v___y_498_ = v___y_563_;
v___y_499_ = v___y_565_;
v___y_500_ = v___y_564_;
v___y_501_ = v___y_566_;
v___y_502_ = v___y_567_;
v___y_503_ = v___x_569_;
goto v___jp_494_;
}
v___jp_573_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_588_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_589_ = lean_string_push(v___x_588_, v___y_584_);
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
v___x_600_ = lean_string_append(v___x_599_, v___y_574_);
v___x_601_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
v___x_603_ = lean_string_append(v___x_602_, v___y_575_);
lean_dec_ref(v___y_575_);
v___x_604_ = lean_string_append(v___x_603_, v___x_601_);
v___x_605_ = lean_string_append(v___x_604_, v_caption_571_);
lean_dec_ref(v_caption_571_);
v___x_606_ = lean_string_append(v___x_605_, v___y_587_);
lean_dec_ref(v___y_587_);
if (v_useAnsi_469_ == 0)
{
v___y_495_ = v___y_578_;
v___y_496_ = v___y_577_;
v___y_497_ = v___y_579_;
v___y_498_ = v___y_580_;
v___y_499_ = v___y_576_;
v___y_500_ = v___y_582_;
v___y_501_ = v___y_585_;
v___y_502_ = v___y_586_;
v___y_503_ = v___x_606_;
goto v___jp_494_;
}
else
{
if (v___y_580_ == 0)
{
if (v___y_581_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_559_ = v___y_577_;
v___y_560_ = v___y_578_;
v___y_561_ = v___y_579_;
v___y_562_ = v___x_606_;
v___y_563_ = v___y_580_;
v___y_564_ = v___y_582_;
v___y_565_ = v___y_576_;
v___y_566_ = v___y_585_;
v___y_567_ = v___y_586_;
v___y_568_ = v___x_607_;
goto v___jp_558_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___y_559_ = v___y_577_;
v___y_560_ = v___y_578_;
v___y_561_ = v___y_579_;
v___y_562_ = v___x_606_;
v___y_563_ = v___y_580_;
v___y_564_ = v___y_582_;
v___y_565_ = v___y_576_;
v___y_566_ = v___y_585_;
v___y_567_ = v___y_586_;
v___y_568_ = v___x_608_;
goto v___jp_558_;
}
}
else
{
lean_object* v___x_609_; 
v___x_609_ = l_Lake_LogLevel_ansiColor(v___y_583_);
v___y_559_ = v___y_577_;
v___y_560_ = v___y_578_;
v___y_561_ = v___y_579_;
v___y_562_ = v___x_606_;
v___y_563_ = v___y_580_;
v___y_564_ = v___y_582_;
v___y_565_ = v___y_576_;
v___y_566_ = v___y_585_;
v___y_567_ = v___y_586_;
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
lean_dec(v___y_634_);
v___y_611_ = v___y_639_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_627_;
v___y_614_ = v___y_628_;
v___y_615_ = v___y_629_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
v___y_619_ = v___y_633_;
v___y_620_ = v___y_635_;
v___y_621_ = v___y_636_;
v___y_622_ = v___y_637_;
v___y_623_ = v___y_638_;
goto v___jp_610_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = lean_nat_dec_lt(v___y_629_, v___y_634_);
if (v___x_640_ == 0)
{
lean_dec(v___y_634_);
v___y_611_ = v___y_639_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_627_;
v___y_614_ = v___y_628_;
v___y_615_ = v___y_629_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
v___y_619_ = v___y_633_;
v___y_620_ = v___y_635_;
v___y_621_ = v___y_636_;
v___y_622_ = v___y_637_;
v___y_623_ = v___y_638_;
goto v___jp_610_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_641_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_642_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_634_);
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
lean_dec_ref(v___x_642_);
v___x_644_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___x_645_ = lean_string_append(v___x_643_, v___x_644_);
v___y_574_ = v___y_639_;
v___y_575_ = v___y_626_;
v___y_576_ = v___y_627_;
v___y_577_ = v___y_628_;
v___y_578_ = v___y_629_;
v___y_579_ = v___y_630_;
v___y_580_ = v___y_631_;
v___y_581_ = v___y_632_;
v___y_582_ = v___y_633_;
v___y_583_ = v___y_635_;
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
v___y_634_ = v___y_655_;
v___y_635_ = v___y_656_;
v___y_636_ = v___y_659_;
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
v___y_634_ = v___y_655_;
v___y_635_ = v___y_656_;
v___y_636_ = v___y_659_;
v___y_637_ = v___y_657_;
v___y_638_ = v___y_658_;
v___y_639_ = v___x_661_;
goto v___jp_625_;
}
}
v___jp_662_:
{
if (v___y_666_ == 0)
{
if (v___y_667_ == 0)
{
uint32_t v___x_675_; 
v___x_675_ = 10004;
v___y_647_ = v___y_674_;
v___y_648_ = v___y_669_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_663_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_667_;
v___y_654_ = v___y_668_;
v___y_655_ = v___y_672_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_673_;
v___y_659_ = v___x_675_;
goto v___jp_646_;
}
else
{
uint32_t v___x_676_; 
v___x_676_ = 8856;
v___y_647_ = v___y_674_;
v___y_648_ = v___y_669_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_663_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_667_;
v___y_654_ = v___y_668_;
v___y_655_ = v___y_672_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_673_;
v___y_659_ = v___x_676_;
goto v___jp_646_;
}
}
else
{
uint32_t v___x_677_; 
v___x_677_ = l_Lake_LogLevel_icon(v___y_671_);
v___y_647_ = v___y_674_;
v___y_648_ = v___y_669_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_663_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_667_;
v___y_654_ = v___y_668_;
v___y_655_ = v___y_672_;
v___y_656_ = v___y_671_;
v___y_657_ = v___y_670_;
v___y_658_ = v___y_673_;
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
v___y_671_ = v___y_687_;
v___y_672_ = v___y_686_;
v___y_673_ = v___y_688_;
v___y_674_ = v___x_690_;
goto v___jp_662_;
}
v___jp_691_:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lake_JobAction_verb(v___y_694_, v___y_699_);
v___y_663_ = v___y_693_;
v___y_664_ = v___y_692_;
v___y_665_ = v___y_694_;
v___y_666_ = v___y_695_;
v___y_667_ = v___y_696_;
v___y_668_ = v___y_697_;
v___y_669_ = v___y_698_;
v___y_670_ = v___y_703_;
v___y_671_ = v___y_701_;
v___y_672_ = v___y_700_;
v___y_673_ = v___y_702_;
v___y_674_ = v___x_704_;
goto v___jp_662_;
}
v___jp_705_:
{
if (v___y_709_ == 0)
{
if (v___y_710_ == 0)
{
if (v_showProgress_470_ == 0)
{
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_706_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_454_ = v___y_707_;
goto v___jp_453_;
}
else
{
if (v_useAnsi_469_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lake_instOrdJobAction_ord(v_minAction_467_, v___y_715_);
if (v___x_717_ == 2)
{
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_706_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_454_ = v___y_707_;
goto v___jp_453_;
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
v___y_699_ = v___y_715_;
v___y_700_ = v___y_714_;
v___y_701_ = v___y_713_;
v___y_702_ = v___y_716_;
v___y_703_ = v_showProgress_470_;
goto v___jp_691_;
}
}
else
{
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_706_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_454_ = v___y_707_;
goto v___jp_453_;
}
}
}
else
{
v___y_679_ = v___y_707_;
v___y_680_ = v___y_706_;
v___y_681_ = v___y_708_;
v___y_682_ = v___y_709_;
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_711_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_713_;
v___y_688_ = v___y_716_;
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
v___y_699_ = v___y_715_;
v___y_700_ = v___y_714_;
v___y_701_ = v___y_713_;
v___y_702_ = v___y_716_;
v___y_703_ = v___y_709_;
goto v___jp_691_;
}
else
{
v___y_679_ = v___y_707_;
v___y_680_ = v___y_706_;
v___y_681_ = v___y_708_;
v___y_682_ = v___y_709_;
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_711_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_713_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_709_;
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
v___y_709_ = v___y_729_;
v___y_710_ = v___y_722_;
v___y_711_ = v___y_723_;
v___y_712_ = v___y_724_;
v___y_713_ = v___y_725_;
v___y_714_ = v___y_726_;
v___y_715_ = v___y_727_;
v___y_716_ = v___y_728_;
goto v___jp_705_;
}
else
{
if (v_showOptional_468_ == 0)
{
lean_dec(v___y_728_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_719_);
lean_dec_ref(v_caption_571_);
lean_dec(v_totalJobs_458_);
lean_dec(v_jobNo_457_);
v___y_454_ = v___y_720_;
goto v___jp_453_;
}
else
{
v___y_706_ = v___y_719_;
v___y_707_ = v___y_720_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_729_;
v___y_710_ = v___y_722_;
v___y_711_ = v___y_723_;
v___y_712_ = v___y_724_;
v___y_713_ = v___y_725_;
v___y_714_ = v___y_726_;
v___y_715_ = v___y_727_;
v___y_716_ = v___y_728_;
goto v___jp_705_;
}
}
}
v___jp_730_:
{
if (v___y_732_ == 0)
{
if (v___y_738_ == 0)
{
v___y_719_ = v___y_731_;
v___y_720_ = v___y_741_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_736_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_738_;
goto v___jp_718_;
}
else
{
uint8_t v___x_742_; 
v___x_742_ = l_Lake_instOrdLogLevel_ord(v_outLv_465_, v___y_737_);
if (v___x_742_ == 2)
{
v___y_719_ = v___y_731_;
v___y_720_ = v___y_741_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_736_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_732_;
goto v___jp_718_;
}
else
{
v___y_719_ = v___y_731_;
v___y_720_ = v___y_741_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_736_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_738_;
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
v___y_719_ = v___y_731_;
v___y_720_ = v___x_755_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_736_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_732_;
goto v___jp_718_;
}
}
}
else
{
v___y_719_ = v___y_731_;
v___y_720_ = v___y_741_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_733_;
v___y_723_ = v___y_734_;
v___y_724_ = v___y_740_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_736_;
v___y_727_ = v___y_735_;
v___y_728_ = v___y_739_;
v___y_729_ = v___y_732_;
goto v___jp_718_;
}
}
}
v___jp_758_:
{
if (v___y_761_ == 0)
{
v___y_731_ = v___y_759_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_768_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_765_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_763_;
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
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*6, v___y_761_);
v___y_731_ = v___y_759_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_768_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_765_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_763_;
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
v___y_731_ = v___y_759_;
v___y_732_ = v___y_760_;
v___y_733_ = v___y_768_;
v___y_734_ = v___y_762_;
v___y_735_ = v___y_765_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_763_;
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
v___x_793_ = lean_strict_and(v___y_790_, v___y_792_);
if (v___y_784_ == 0)
{
v___y_759_ = v___y_783_;
v___y_760_ = v___x_793_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_788_;
v___y_765_ = v___y_787_;
v___y_766_ = v___y_790_;
v___y_767_ = v___y_791_;
v___y_768_ = v___y_784_;
goto v___jp_758_;
}
else
{
if (v___x_793_ == 0)
{
v___y_759_ = v___y_783_;
v___y_760_ = v___x_793_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_788_;
v___y_765_ = v___y_787_;
v___y_766_ = v___y_790_;
v___y_767_ = v___y_791_;
v___y_768_ = v___y_784_;
goto v___jp_758_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
v___y_759_ = v___y_783_;
v___y_760_ = v___x_793_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v___y_763_ = v___y_789_;
v___y_764_ = v___y_788_;
v___y_765_ = v___y_787_;
v___y_766_ = v___y_790_;
v___y_767_ = v___y_791_;
v___y_768_ = v___x_794_;
goto v___jp_758_;
}
}
}
v___jp_795_:
{
uint8_t v___x_805_; 
v___x_805_ = l_Lake_instOrdLogLevel_ord(v_failLv_466_, v___y_800_);
if (v___x_805_ == 2)
{
uint8_t v___x_806_; 
v___x_806_ = 0;
v___y_783_ = v___y_796_;
v___y_784_ = v___y_797_;
v___y_785_ = v___y_798_;
v___y_786_ = v___y_799_;
v___y_787_ = v___y_802_;
v___y_788_ = v___y_801_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_804_;
v___y_791_ = v___y_803_;
v___y_792_ = v___x_806_;
goto v___jp_782_;
}
else
{
uint8_t v___x_807_; 
v___x_807_ = 1;
v___y_783_ = v___y_796_;
v___y_784_ = v___y_797_;
v___y_785_ = v___y_798_;
v___y_786_ = v___y_799_;
v___y_787_ = v___y_802_;
v___y_788_ = v___y_801_;
v___y_789_ = v___y_800_;
v___y_790_ = v___y_804_;
v___y_791_ = v___y_803_;
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
v___y_796_ = v___x_817_;
v___y_797_ = v_canceled_813_;
v___y_798_ = v_wantsRebuild_812_;
v___y_799_ = v_log_810_;
v___y_800_ = v___x_815_;
v___y_801_ = v_buildTime_814_;
v___y_802_ = v_action_811_;
v___y_803_ = v___x_816_;
v___y_804_ = v___x_819_;
goto v___jp_795_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = 0;
v___y_796_ = v___x_817_;
v___y_797_ = v_canceled_813_;
v___y_798_ = v_wantsRebuild_812_;
v___y_799_ = v_log_810_;
v___y_800_ = v___x_815_;
v___y_801_ = v_buildTime_814_;
v___y_802_ = v_action_811_;
v___y_803_ = v___x_816_;
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
uint8_t v___y_15078__boxed_849_; uint8_t v_useAnsi_15079__boxed_850_; size_t v_i_boxed_851_; size_t v_stop_boxed_852_; lean_object* v_res_853_; 
v___y_15078__boxed_849_ = lean_unbox(v___y_840_);
v_useAnsi_15079__boxed_850_ = lean_unbox(v_useAnsi_841_);
v_i_boxed_851_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_stop_boxed_852_ = lean_unbox_usize(v_stop_844_);
lean_dec(v_stop_844_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_839_, v___y_15078__boxed_849_, v_useAnsi_15079__boxed_850_, v_as_842_, v_i_boxed_851_, v_stop_boxed_852_, v_b_845_, v___y_846_, v___y_847_);
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
lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v_fst_963_; lean_object* v_snd_964_; lean_object* v___y_975_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_978_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_979_ = lean_array_get_size(v_unfinished_956_);
v___x_980_ = lean_nat_dec_lt(v___x_960_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_inc_ref(v_a_958_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v_a_958_);
v___y_962_ = v___x_981_;
v_fst_963_ = v___x_978_;
v_snd_964_ = v_a_958_;
goto v___jp_961_;
}
else
{
uint8_t v___x_982_; 
v___x_982_ = lean_nat_dec_le(v___x_979_, v___x_979_);
if (v___x_982_ == 0)
{
if (v___x_980_ == 0)
{
lean_object* v___x_983_; 
lean_inc_ref(v_a_958_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_978_);
lean_ctor_set(v___x_983_, 1, v_a_958_);
v___y_962_ = v___x_983_;
v_fst_963_ = v___x_978_;
v_snd_964_ = v_a_958_;
goto v___jp_961_;
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_979_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_956_, v___x_984_, v___x_985_, v___x_978_, v_a_957_, v_a_958_);
v___y_975_ = v___x_986_;
goto v___jp_974_;
}
}
else
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((size_t)0ULL);
v___x_988_ = lean_usize_of_nat(v___x_979_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_956_, v___x_987_, v___x_988_, v___x_978_, v_a_957_, v_a_958_);
v___y_975_ = v___x_989_;
goto v___jp_974_;
}
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
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_le(v___x_965_, v___x_965_);
if (v___x_967_ == 0)
{
if (v___x_966_ == 0)
{
lean_dec_ref(v_snd_964_);
lean_dec_ref(v_fst_963_);
return v___y_962_;
}
else
{
size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; 
lean_dec_ref(v___y_962_);
v___x_968_ = ((size_t)0ULL);
v___x_969_ = lean_usize_of_nat(v___x_965_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_955_, v___x_968_, v___x_969_, v_fst_963_, v_a_957_, v_snd_964_);
return v___x_970_;
}
}
else
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v___y_962_);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = lean_usize_of_nat(v___x_965_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_955_, v___x_971_, v___x_972_, v_fst_963_, v_a_957_, v_snd_964_);
return v___x_973_;
}
}
}
v___jp_974_:
{
lean_object* v_fst_976_; lean_object* v_snd_977_; 
v_fst_976_ = lean_ctor_get(v___y_975_, 0);
lean_inc(v_fst_976_);
v_snd_977_ = lean_ctor_get(v___y_975_, 1);
lean_inc(v_snd_977_);
v___y_962_ = v___y_975_;
v_fst_963_ = v_fst_976_;
v_snd_964_ = v_snd_977_;
goto v___jp_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_990_, lean_object* v_unfinished_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_990_, v_unfinished_991_, v_a_992_, v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec_ref(v_unfinished_991_);
lean_dec_ref(v_new_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___y_1000_; lean_object* v___x_1018_; lean_object* v_lastUpdate_1019_; lean_object* v_updateFrequency_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1018_ = lean_io_mono_ms_now();
v_lastUpdate_1019_ = lean_ctor_get(v_a_997_, 4);
v_updateFrequency_1020_ = lean_ctor_get(v_a_996_, 2);
v___x_1021_ = lean_nat_sub(v___x_1018_, v_lastUpdate_1019_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_nat_sub(v_updateFrequency_1020_, v___x_1021_);
lean_dec(v___x_1021_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_nat_dec_lt(v___x_1023_, v___x_1022_);
if (v___x_1024_ == 0)
{
lean_dec(v___x_1022_);
v___y_1000_ = v_a_997_;
goto v___jp_999_;
}
else
{
uint32_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_uint32_of_nat(v___x_1022_);
lean_dec(v___x_1022_);
v___x_1026_ = l_IO_sleep(v___x_1025_);
v___y_1000_ = v_a_997_;
goto v___jp_999_;
}
v___jp_999_:
{
lean_object* v___x_1001_; lean_object* v_jobNo_1002_; lean_object* v_totalJobs_1003_; uint8_t v_wantsRebuild_1004_; lean_object* v_failures_1005_; lean_object* v_resetCtrl_1006_; lean_object* v_spinnerIdx_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1016_; 
v___x_1001_ = lean_io_mono_ms_now();
v_jobNo_1002_ = lean_ctor_get(v___y_1000_, 0);
v_totalJobs_1003_ = lean_ctor_get(v___y_1000_, 1);
v_wantsRebuild_1004_ = lean_ctor_get_uint8(v___y_1000_, sizeof(void*)*6);
v_failures_1005_ = lean_ctor_get(v___y_1000_, 2);
v_resetCtrl_1006_ = lean_ctor_get(v___y_1000_, 3);
v_spinnerIdx_1007_ = lean_ctor_get(v___y_1000_, 5);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___y_1000_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v___y_1000_, 4);
lean_dec(v_unused_1017_);
v___x_1009_ = v___y_1000_;
v_isShared_1010_ = v_isSharedCheck_1016_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_spinnerIdx_1007_);
lean_inc(v_resetCtrl_1006_);
lean_inc(v_failures_1005_);
lean_inc(v_totalJobs_1003_);
lean_inc(v_jobNo_1002_);
lean_dec(v___y_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1016_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_box(0);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 4, v___x_1001_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_jobNo_1002_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_totalJobs_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_failures_1005_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_resetCtrl_1006_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1015_, 5, v_spinnerIdx_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*6, v_wantsRebuild_1004_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1027_, v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_1031_, lean_object* v_unfinished_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v_failFast_1069_; 
v___x_1036_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_1031_, v_unfinished_1032_, v_a_1033_, v_a_1034_);
lean_dec_ref(v_unfinished_1032_);
lean_dec_ref(v_new_1031_);
v_fst_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_fst_1037_);
v_snd_1038_ = lean_ctor_get(v___x_1036_, 1);
lean_inc(v_snd_1038_);
lean_dec_ref(v___x_1036_);
v_fst_1039_ = lean_ctor_get(v_fst_1037_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v_fst_1037_, 1);
lean_inc(v_snd_1040_);
lean_dec(v_fst_1037_);
v_failFast_1069_ = lean_ctor_get_uint8(v_a_1033_, sizeof(void*)*4 + 7);
if (v_failFast_1069_ == 0)
{
v___y_1042_ = v_a_1033_;
v___y_1043_ = v_snd_1038_;
goto v___jp_1041_;
}
else
{
lean_object* v_cancelTk_x3f_1070_; 
v_cancelTk_x3f_1070_ = lean_ctor_get(v_a_1033_, 3);
if (lean_obj_tag(v_cancelTk_x3f_1070_) == 1)
{
lean_object* v_val_1071_; lean_object* v_failures_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_val_1071_ = lean_ctor_get(v_cancelTk_x3f_1070_, 0);
v_failures_1072_ = lean_ctor_get(v_snd_1038_, 2);
v___x_1073_ = lean_array_get_size(v_failures_1072_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_nat_dec_eq(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = l_IO_CancelToken_set(v_val_1071_);
v___y_1042_ = v_a_1033_;
v___y_1043_ = v_snd_1038_;
goto v___jp_1041_;
}
else
{
v___y_1042_ = v_a_1033_;
v___y_1043_ = v_snd_1038_;
goto v___jp_1041_;
}
}
else
{
v___y_1042_ = v_a_1033_;
v___y_1043_ = v_snd_1038_;
goto v___jp_1041_;
}
}
v___jp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_array_get_size(v_snd_1040_);
v___x_1046_ = lean_nat_dec_lt(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v_fst_1039_);
v___x_1047_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1042_, v___y_1043_);
v_fst_1048_ = lean_ctor_get(v___x_1047_, 0);
v_snd_1049_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1060_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_inc(v_fst_1048_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1060_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = lean_array_get_size(v_fst_1048_);
v___x_1054_ = lean_nat_dec_lt(v___x_1044_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_dec(v_fst_1048_);
lean_dec(v_snd_1040_);
v___x_1055_ = lean_box(0);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1055_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_snd_1049_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
else
{
lean_del_object(v___x_1051_);
v_new_1031_ = v_fst_1048_;
v_unfinished_1032_ = v_snd_1040_;
v_a_1033_ = v___y_1042_;
v_a_1034_ = v_snd_1049_;
goto _start;
}
}
}
else
{
lean_object* v___x_1061_; lean_object* v_snd_1062_; lean_object* v___x_1063_; lean_object* v_snd_1064_; lean_object* v___x_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; 
v___x_1061_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1039_, v_snd_1040_, v___y_1042_, v___y_1043_);
lean_dec(v_fst_1039_);
v_snd_1062_ = lean_ctor_get(v___x_1061_, 1);
lean_inc(v_snd_1062_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v___y_1042_, v_snd_1062_);
v_snd_1064_ = lean_ctor_get(v___x_1063_, 1);
lean_inc(v_snd_1064_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1042_, v_snd_1064_);
v_fst_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_snd_1067_);
lean_dec_ref(v___x_1065_);
v_new_1031_ = v_fst_1066_;
v_unfinished_1032_ = v_snd_1040_;
v_a_1033_ = v___y_1042_;
v_a_1034_ = v_snd_1067_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1077_, lean_object* v_unfinished_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1077_, v_unfinished_1078_, v_a_1079_, v_a_1080_);
lean_dec_ref(v_a_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1158_; 
v___x_1087_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1084_, v_a_1085_);
v_fst_1088_ = lean_ctor_get(v___x_1087_, 0);
v_snd_1089_ = lean_ctor_get(v___x_1087_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1158_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_inc(v_fst_1088_);
lean_dec(v___x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1158_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1156_; 
v___x_1093_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1088_, v_init_1083_, v_a_1084_, v_snd_1089_);
v_snd_1094_ = lean_ctor_get(v___x_1093_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1157_);
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1156_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1156_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_jobNo_1098_; lean_object* v_totalJobs_1099_; uint8_t v_wantsRebuild_1100_; lean_object* v_failures_1101_; lean_object* v_resetCtrl_1102_; lean_object* v_lastUpdate_1103_; lean_object* v_spinnerIdx_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1155_; 
v_jobNo_1098_ = lean_ctor_get(v_snd_1094_, 0);
v_totalJobs_1099_ = lean_ctor_get(v_snd_1094_, 1);
v_wantsRebuild_1100_ = lean_ctor_get_uint8(v_snd_1094_, sizeof(void*)*6);
v_failures_1101_ = lean_ctor_get(v_snd_1094_, 2);
v_resetCtrl_1102_ = lean_ctor_get(v_snd_1094_, 3);
v_lastUpdate_1103_ = lean_ctor_get(v_snd_1094_, 4);
v_spinnerIdx_1104_ = lean_ctor_get(v_snd_1094_, 5);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_snd_1094_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1106_ = v_snd_1094_;
v_isShared_1107_ = v_isSharedCheck_1155_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_spinnerIdx_1104_);
lean_inc(v_lastUpdate_1103_);
lean_inc(v_resetCtrl_1102_);
lean_inc(v_failures_1101_);
lean_inc(v_totalJobs_1099_);
lean_inc(v_jobNo_1098_);
lean_dec(v_snd_1094_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1155_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 3, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_jobNo_1098_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_totalJobs_1099_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_failures_1101_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_lastUpdate_1103_);
lean_ctor_set(v_reuseFailAlloc_1154_, 5, v_spinnerIdx_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*6, v_wantsRebuild_1100_);
v___x_1110_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v_val_1112_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_string_utf8_byte_size(v_resetCtrl_1102_);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_nat_dec_eq(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v_out_1119_; lean_object* v_flush_1120_; lean_object* v_putStr_1121_; lean_object* v___x_1126_; 
lean_del_object(v___x_1091_);
v_out_1119_ = lean_ctor_get(v_a_1084_, 1);
v_flush_1120_ = lean_ctor_get(v_out_1119_, 0);
v_putStr_1121_ = lean_ctor_get(v_out_1119_, 4);
lean_inc_ref(v_putStr_1121_);
lean_inc_ref(v_resetCtrl_1102_);
v___x_1126_ = lean_apply_2(v_putStr_1121_, v_resetCtrl_1102_, lean_box(0));
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_dec_ref_known(v___x_1126_, 1);
lean_dec_ref(v_resetCtrl_1102_);
goto v___jp_1122_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1149_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1149_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1149_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1132_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1133_ = lean_unsigned_to_nat(82u);
v___x_1134_ = lean_unsigned_to_nat(4u);
v___x_1135_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1136_ = lean_io_error_to_string(v_a_1127_);
v___x_1137_ = lean_string_append(v___x_1135_, v___x_1136_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
v___x_1140_ = l_String_quote(v_resetCtrl_1102_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 3);
lean_ctor_set(v___x_1129_, 0, v___x_1140_);
v___x_1142_ = v___x_1129_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1143_ = l_Std_Format_defWidth;
v___x_1144_ = l_Std_Format_pretty(v___x_1142_, v___x_1143_, v___x_1117_, v___x_1117_);
v___x_1145_ = lean_string_append(v___x_1139_, v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = l_mkPanicMessageWithDecl(v___x_1131_, v___x_1132_, v___x_1133_, v___x_1134_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1146_);
goto v___jp_1122_;
}
}
}
v___jp_1122_:
{
lean_object* v___x_1123_; 
lean_inc_ref(v_flush_1120_);
v___x_1123_ = lean_apply_1(v_flush_1120_, lean_box(0));
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v_val_1112_ = v_a_1124_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_box(0);
v_val_1112_ = v___x_1125_;
goto v___jp_1111_;
}
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec_ref(v_resetCtrl_1102_);
lean_del_object(v___x_1096_);
v___x_1150_ = lean_box(0);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1110_);
lean_ctor_set(v___x_1091_, 0, v___x_1150_);
v___x_1152_ = v___x_1091_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1110_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
v___jp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1110_);
lean_ctor_set(v___x_1096_, 0, v_val_1112_);
v___x_1114_ = v___x_1096_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_val_1112_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1110_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1159_, v_a_1160_, v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1164_){
_start:
{
lean_object* v_failures_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_failures_1165_ = lean_ctor_get(v_self_1164_, 0);
v___x_1166_ = lean_array_get_size(v_failures_1165_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_nat_dec_eq(v___x_1166_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1169_);
lean_dec_ref(v_self_1169_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1172_, lean_object* v_jobs_1173_, lean_object* v_cancelTk_x3f_1174_){
_start:
{
lean_object* v_toLogConfig_1176_; uint8_t v_failFast_1177_; uint8_t v_verbosity_1178_; uint8_t v_failLv_1179_; uint8_t v_outLv_1180_; uint8_t v_ansiMode_1181_; lean_object* v_out_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___y_1191_; uint8_t v___y_1192_; uint8_t v___y_1196_; 
v_toLogConfig_1176_ = lean_ctor_get(v_cfg_1172_, 0);
v_failFast_1177_ = lean_ctor_get_uint8(v_cfg_1172_, sizeof(void*)*5 + 3);
v_verbosity_1178_ = lean_ctor_get_uint8(v_cfg_1172_, sizeof(void*)*5 + 4);
v_failLv_1179_ = lean_ctor_get_uint8(v_toLogConfig_1176_, sizeof(void*)*1);
v_outLv_1180_ = lean_ctor_get_uint8(v_toLogConfig_1176_, sizeof(void*)*1 + 1);
v_ansiMode_1181_ = lean_ctor_get_uint8(v_toLogConfig_1176_, sizeof(void*)*1 + 2);
v_out_1182_ = lean_ctor_get(v_toLogConfig_1176_, 0);
v___x_1183_ = l_Lake_OutStream_get(v_out_1182_);
lean_inc_ref(v___x_1183_);
v___x_1184_ = l_Lake_AnsiMode_isEnabled(v___x_1183_, v_ansiMode_1181_);
v___x_1185_ = l_Lake_BuildConfig_showProgress(v_cfg_1172_);
v___x_1186_ = lean_box(v_verbosity_1178_);
v___x_1187_ = lean_obj_tag_nat(v___x_1186_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(2u);
v___x_1189_ = lean_nat_dec_eq(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = 3;
v___y_1196_ = v___x_1198_;
goto v___jp_1195_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = 0;
v___y_1196_ = v___x_1199_;
goto v___jp_1195_;
}
v___jp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_unsigned_to_nat(100u);
v___x_1194_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_1194_, 0, v_jobs_1173_);
lean_ctor_set(v___x_1194_, 1, v___x_1183_);
lean_ctor_set(v___x_1194_, 2, v___x_1193_);
lean_ctor_set(v___x_1194_, 3, v_cancelTk_x3f_1174_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4, v_outLv_1180_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 1, v_failLv_1179_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 2, v___y_1191_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 3, v___x_1189_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 4, v___x_1184_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 5, v___x_1185_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 6, v___y_1192_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*4 + 7, v_failFast_1177_);
return v___x_1194_;
}
v___jp_1195_:
{
if (v___x_1189_ == 0)
{
if (v___x_1184_ == 0)
{
uint8_t v___x_1197_; 
v___x_1197_ = 1;
v___y_1191_ = v___y_1196_;
v___y_1192_ = v___x_1197_;
goto v___jp_1190_;
}
else
{
v___y_1191_ = v___y_1196_;
v___y_1192_ = v___x_1189_;
goto v___jp_1190_;
}
}
else
{
v___y_1191_ = v___y_1196_;
v___y_1192_ = v___x_1189_;
goto v___jp_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1200_, lean_object* v_jobs_1201_, lean_object* v_cancelTk_x3f_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1200_, v_jobs_1201_, v_cancelTk_x3f_1202_);
lean_dec_ref(v_cfg_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1205_, lean_object* v_initJobs_1206_, lean_object* v_initFailures_1207_, lean_object* v_resetCtrl_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_snd_1215_; lean_object* v_totalJobs_1216_; uint8_t v_wantsRebuild_1217_; lean_object* v_failures_1218_; lean_object* v___x_1219_; 
v___x_1210_ = lean_io_mono_ms_now();
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = 0;
v___x_1213_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1211_);
lean_ctor_set(v___x_1213_, 2, v_initFailures_1207_);
lean_ctor_set(v___x_1213_, 3, v_resetCtrl_1208_);
lean_ctor_set(v___x_1213_, 4, v___x_1210_);
lean_ctor_set(v___x_1213_, 5, v___x_1211_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*6, v___x_1212_);
v___x_1214_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1206_, v_ctx_1205_, v___x_1213_);
v_snd_1215_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_snd_1215_);
lean_dec_ref(v___x_1214_);
v_totalJobs_1216_ = lean_ctor_get(v_snd_1215_, 1);
lean_inc(v_totalJobs_1216_);
v_wantsRebuild_1217_ = lean_ctor_get_uint8(v_snd_1215_, sizeof(void*)*6);
v_failures_1218_ = lean_ctor_get(v_snd_1215_, 2);
lean_inc_ref(v_failures_1218_);
lean_dec(v_snd_1215_);
v___x_1219_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1219_, 0, v_failures_1218_);
lean_ctor_set(v___x_1219_, 1, v_totalJobs_1216_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*2, v_wantsRebuild_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1220_, lean_object* v_initJobs_1221_, lean_object* v_initFailures_1222_, lean_object* v_resetCtrl_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1220_, v_initJobs_1221_, v_initFailures_1222_, v_resetCtrl_1223_);
lean_dec_ref(v_ctx_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1226_, lean_object* v_jobs_1227_, lean_object* v_out_1228_, uint8_t v_failLv_1229_, uint8_t v_outLv_1230_, uint8_t v_minAction_1231_, uint8_t v_showOptional_1232_, uint8_t v_useAnsi_1233_, uint8_t v_showProgress_1234_, uint8_t v_showTime_1235_, lean_object* v_resetCtrl_1236_, lean_object* v_initFailures_1237_, lean_object* v_updateFrequency_1238_){
_start:
{
uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v_ctx_1242_; lean_object* v___x_1243_; 
v___x_1240_ = 0;
v___x_1241_ = lean_box(0);
v_ctx_1242_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_ctx_1242_, 0, v_jobs_1227_);
lean_ctor_set(v_ctx_1242_, 1, v_out_1228_);
lean_ctor_set(v_ctx_1242_, 2, v_updateFrequency_1238_);
lean_ctor_set(v_ctx_1242_, 3, v___x_1241_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4, v_outLv_1230_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 1, v_failLv_1229_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 2, v_minAction_1231_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 3, v_showOptional_1232_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 4, v_useAnsi_1233_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 5, v_showProgress_1234_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 6, v_showTime_1235_);
lean_ctor_set_uint8(v_ctx_1242_, sizeof(void*)*4 + 7, v___x_1240_);
v___x_1243_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1242_, v_initJobs_1226_, v_initFailures_1237_, v_resetCtrl_1236_);
lean_dec_ref_known(v_ctx_1242_, 4);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1244_, lean_object* v_jobs_1245_, lean_object* v_out_1246_, lean_object* v_failLv_1247_, lean_object* v_outLv_1248_, lean_object* v_minAction_1249_, lean_object* v_showOptional_1250_, lean_object* v_useAnsi_1251_, lean_object* v_showProgress_1252_, lean_object* v_showTime_1253_, lean_object* v_resetCtrl_1254_, lean_object* v_initFailures_1255_, lean_object* v_updateFrequency_1256_, lean_object* v_a_1257_){
_start:
{
uint8_t v_failLv_boxed_1258_; uint8_t v_outLv_boxed_1259_; uint8_t v_minAction_boxed_1260_; uint8_t v_showOptional_boxed_1261_; uint8_t v_useAnsi_boxed_1262_; uint8_t v_showProgress_boxed_1263_; uint8_t v_showTime_boxed_1264_; lean_object* v_res_1265_; 
v_failLv_boxed_1258_ = lean_unbox(v_failLv_1247_);
v_outLv_boxed_1259_ = lean_unbox(v_outLv_1248_);
v_minAction_boxed_1260_ = lean_unbox(v_minAction_1249_);
v_showOptional_boxed_1261_ = lean_unbox(v_showOptional_1250_);
v_useAnsi_boxed_1262_ = lean_unbox(v_useAnsi_1251_);
v_showProgress_boxed_1263_ = lean_unbox(v_showProgress_1252_);
v_showTime_boxed_1264_ = lean_unbox(v_showTime_1253_);
v_res_1265_ = l_Lake_monitorJobs(v_initJobs_1244_, v_jobs_1245_, v_out_1246_, v_failLv_boxed_1258_, v_outLv_boxed_1259_, v_minAction_boxed_1260_, v_showOptional_boxed_1261_, v_useAnsi_boxed_1262_, v_showProgress_boxed_1263_, v_showTime_boxed_1264_, v_resetCtrl_1254_, v_initFailures_1255_, v_updateFrequency_1256_);
return v_res_1265_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1266_; 
v___x_1266_ = 3;
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(lean_object* v_logger_1267_, lean_object* v_x_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_apply_2(v_logger_1267_, v___y_1269_, lean_box(0));
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed(lean_object* v_logger_1272_, lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(v_logger_1272_, v_x_1273_, v___y_1274_);
return v_res_1276_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1279_ = l_String_quote(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1);
v___x_1281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = l_Std_Format_defWidth;
v___x_1284_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2);
v___x_1285_ = l_Std_Format_pretty(v___x_1284_, v___x_1283_, v___x_1282_, v___x_1282_);
return v___x_1285_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1293_ = l_String_quote(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8);
v___x_1295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = l_Std_Format_defWidth;
v___x_1298_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9);
v___x_1299_ = l_Std_Format_pretty(v___x_1298_, v___x_1297_, v___x_1296_, v___x_1296_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1302_ = l_String_quote(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12);
v___x_1304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = l_Std_Format_defWidth;
v___x_1307_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13);
v___x_1308_ = l_Std_Format_pretty(v___x_1307_, v___x_1306_, v___x_1305_, v___x_1305_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1312_ = l_String_quote(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17);
v___x_1314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = l_Std_Format_defWidth;
v___x_1317_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18);
v___x_1318_ = l_Std_Format_pretty(v___x_1317_, v___x_1316_, v___x_1315_, v___x_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(lean_object* v_logger_1319_, lean_object* v_bctx_1320_, lean_object* v_out_1321_, lean_object* v_outputsFile_1322_){
_start:
{
lean_object* v___x_1330_; lean_object* v_outputsRef_x3f_1331_; 
v___x_1330_ = l_instMonadBaseIO;
v_outputsRef_x3f_1331_ = lean_ctor_get(v_bctx_1320_, 5);
lean_inc(v_outputsRef_x3f_1331_);
if (lean_obj_tag(v_outputsRef_x3f_1331_) == 1)
{
lean_object* v_toContext_1332_; lean_object* v_toBuildConfig_1333_; lean_object* v_val_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1481_; 
v_toContext_1332_ = lean_ctor_get(v_bctx_1320_, 1);
lean_inc(v_toContext_1332_);
v_toBuildConfig_1333_ = lean_ctor_get(v_bctx_1320_, 0);
lean_inc_ref(v_toBuildConfig_1333_);
lean_dec_ref(v_bctx_1320_);
v_val_1334_ = lean_ctor_get(v_outputsRef_x3f_1331_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_outputsRef_x3f_1331_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1336_ = v_outputsRef_x3f_1331_;
v_isShared_1337_ = v_isSharedCheck_1481_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_val_1334_);
lean_dec(v_outputsRef_x3f_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1481_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_lakeEnv_1338_; lean_object* v_packages_1339_; uint8_t v_verbosity_1340_; lean_object* v_outputsIdx_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_lakeEnv_1338_ = lean_ctor_get(v_toContext_1332_, 0);
lean_inc_ref(v_lakeEnv_1338_);
v_packages_1339_ = lean_ctor_get(v_toContext_1332_, 4);
lean_inc_ref(v_packages_1339_);
lean_dec(v_toContext_1332_);
v_verbosity_1340_ = lean_ctor_get_uint8(v_toBuildConfig_1333_, sizeof(void*)*5 + 4);
v_outputsIdx_1341_ = lean_ctor_get(v_toBuildConfig_1333_, 2);
lean_inc(v_outputsIdx_1341_);
lean_dec_ref(v_toBuildConfig_1333_);
v___x_1342_ = lean_array_get_size(v_packages_1339_);
v___x_1343_ = lean_nat_dec_lt(v_outputsIdx_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_object* v_putStr_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v_outputsIdx_1341_);
lean_dec_ref(v_packages_1339_);
lean_dec_ref(v_lakeEnv_1338_);
lean_del_object(v___x_1336_);
lean_dec(v_val_1334_);
lean_dec_ref(v_outputsFile_1322_);
lean_dec_ref(v_logger_1319_);
v_putStr_1344_ = lean_ctor_get(v_out_1321_, 4);
lean_inc_ref(v_putStr_1344_);
lean_dec_ref(v_out_1321_);
v___x_1345_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1346_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1347_ = lean_apply_2(v_putStr_1344_, v___x_1345_, lean_box(0));
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_dec_ref_known(v___x_1347_, 1);
goto v___jp_1326_;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_2543__overap_1361_; lean_object* v___x_1362_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1350_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1351_ = lean_unsigned_to_nat(82u);
v___x_1352_ = lean_unsigned_to_nat(4u);
v___x_1353_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1354_ = lean_io_error_to_string(v_a_1348_);
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
v___x_1360_ = l_mkPanicMessageWithDecl(v___x_1349_, v___x_1350_, v___x_1351_, v___x_1352_, v___x_1359_);
lean_dec_ref(v___x_1359_);
v___x_2543__overap_1361_ = l_panic___redArg(v___x_1346_, v___x_1360_);
v___x_1362_ = lean_apply_1(v___x_2543__overap_1361_, lean_box(0));
lean_dec(v___x_1362_);
goto v___jp_1326_;
}
}
else
{
lean_object* v___x_1363_; lean_object* v_config_1364_; lean_object* v_enableArtifactCache_x3f_1365_; lean_object* v___f_1366_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1390_; uint8_t v___y_1459_; uint8_t v___y_1468_; 
v___x_1363_ = lean_array_fget(v_packages_1339_, v_outputsIdx_1341_);
lean_dec(v_outputsIdx_1341_);
v_config_1364_ = lean_ctor_get(v___x_1363_, 6);
v_enableArtifactCache_x3f_1365_ = lean_ctor_get(v_config_1364_, 24);
lean_inc_ref(v_logger_1319_);
v___f_1366_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1366_, 0, v_logger_1319_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1365_) == 0)
{
lean_object* v_enableArtifactCache_x3f_1469_; 
v_enableArtifactCache_x3f_1469_ = lean_ctor_get(v_lakeEnv_1338_, 6);
lean_inc(v_enableArtifactCache_x3f_1469_);
lean_dec_ref(v_lakeEnv_1338_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_config_1472_; lean_object* v_enableArtifactCache_x3f_1473_; 
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_array_fget(v_packages_1339_, v___x_1470_);
lean_dec_ref(v_packages_1339_);
v_config_1472_ = lean_ctor_get(v___x_1471_, 6);
lean_inc_ref(v_config_1472_);
lean_dec(v___x_1471_);
v_enableArtifactCache_x3f_1473_ = lean_ctor_get(v_config_1472_, 24);
lean_inc(v_enableArtifactCache_x3f_1473_);
lean_dec_ref(v_config_1472_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1473_) == 0)
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
v___y_1459_ = v___x_1474_;
goto v___jp_1458_;
}
else
{
lean_object* v_val_1475_; uint8_t v___x_1476_; 
v_val_1475_ = lean_ctor_get(v_enableArtifactCache_x3f_1473_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1473_, 1);
v___x_1476_ = lean_unbox(v_val_1475_);
lean_dec(v_val_1475_);
v___y_1468_ = v___x_1476_;
goto v___jp_1467_;
}
}
else
{
lean_object* v_val_1477_; uint8_t v___x_1478_; 
lean_dec_ref(v_packages_1339_);
v_val_1477_ = lean_ctor_get(v_enableArtifactCache_x3f_1469_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1469_, 1);
v___x_1478_ = lean_unbox(v_val_1477_);
lean_dec(v_val_1477_);
v___y_1468_ = v___x_1478_;
goto v___jp_1467_;
}
}
else
{
lean_object* v_val_1479_; uint8_t v___x_1480_; 
lean_dec_ref(v_packages_1339_);
lean_dec_ref(v_lakeEnv_1338_);
v_val_1479_ = lean_ctor_get(v_enableArtifactCache_x3f_1365_, 0);
v___x_1480_ = lean_unbox(v_val_1479_);
v___y_1468_ = v___x_1480_;
goto v___jp_1467_;
}
v___jp_1367_:
{
if (v___y_1369_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v___y_1368_);
lean_dec_ref(v___f_1366_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_array_get_size(v___y_1368_);
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_nat_dec_lt(v___y_1370_, v___x_1372_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v___y_1368_);
lean_dec_ref(v___f_1366_);
return v___x_1373_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_2357__overap_1377_; lean_object* v___x_1378_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1372_);
v___x_2357__overap_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1330_, v___f_1366_, v___y_1368_, v___x_1375_, v___x_1376_, v___x_1373_);
v___x_1378_ = lean_apply_1(v___x_2357__overap_1377_, lean_box(0));
return v___x_1378_;
}
}
}
v___jp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1382_ = lean_array_get_size(v___y_1381_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_nat_dec_lt(v___y_1380_, v___x_1382_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v___y_1381_);
lean_dec_ref(v___f_1366_);
return v___x_1383_;
}
else
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_2287__overap_1387_; lean_object* v___x_1388_; 
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = lean_usize_of_nat(v___x_1382_);
v___x_2287__overap_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1330_, v___f_1366_, v___y_1381_, v___x_1385_, v___x_1386_, v___x_1383_);
v___x_1388_ = lean_apply_1(v___x_2287__overap_1387_, lean_box(0));
return v___x_1388_;
}
}
v___jp_1389_:
{
lean_object* v___x_1391_; lean_object* v_config_1392_; lean_object* v_toLeanConfig_1393_; lean_object* v_platformIndependent_1394_; lean_object* v___f_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1391_ = lean_st_ref_get(v_val_1334_);
lean_dec(v_val_1334_);
v_config_1392_ = lean_ctor_get(v___x_1363_, 6);
lean_inc_ref(v_config_1392_);
lean_dec(v___x_1363_);
v_toLeanConfig_1393_ = lean_ctor_get(v_config_1392_, 1);
lean_inc_ref(v_toLeanConfig_1393_);
lean_dec_ref(v_config_1392_);
v_platformIndependent_1394_ = lean_ctor_get(v_toLeanConfig_1393_, 10);
lean_inc(v_platformIndependent_1394_);
lean_dec_ref(v_toLeanConfig_1393_);
v___f_1395_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5));
v___x_1396_ = lean_box(v___x_1343_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1396_);
v___x_1398_ = v___x_1336_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1399_ = l_instBEqOption_beq___redArg(v___f_1395_, v_platformIndependent_1394_, v___x_1398_);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_1402_ = l_Lake_CacheMap_writeFile(v_outputsFile_1322_, v___x_1391_, v___x_1399_, v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 2);
v___x_1404_ = lean_array_get_size(v_a_1403_);
v___x_1405_ = lean_nat_dec_eq(v___x_1404_, v___x_1400_);
if (v___x_1405_ == 0)
{
if (v___y_1390_ == 0)
{
lean_dec(v_a_1403_);
lean_dec_ref(v___f_1366_);
lean_dec_ref(v_out_1321_);
goto v___jp_1324_;
}
else
{
lean_object* v_putStr_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_putStr_1406_ = lean_ctor_get(v_out_1321_, 4);
lean_inc_ref(v_putStr_1406_);
lean_dec_ref(v_out_1321_);
v___x_1407_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1408_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1409_ = lean_apply_2(v_putStr_1406_, v___x_1407_, lean_box(0));
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_dec_ref_known(v___x_1409_, 1);
v___y_1380_ = v___x_1400_;
v___y_1381_ = v_a_1403_;
goto v___jp_1379_;
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_2551__overap_1428_; lean_object* v___x_1429_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1412_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1413_ = lean_unsigned_to_nat(82u);
v___x_1414_ = lean_unsigned_to_nat(4u);
v___x_1415_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1416_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1416_, v___y_1390_);
v___x_1418_ = lean_string_append(v___x_1415_, v___x_1417_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1420_ = lean_string_append(v___x_1418_, v___x_1419_);
v___x_1421_ = lean_io_error_to_string(v_a_1410_);
v___x_1422_ = lean_string_append(v___x_1420_, v___x_1421_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
v___x_1425_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_1426_ = lean_string_append(v___x_1424_, v___x_1425_);
v___x_1427_ = l_mkPanicMessageWithDecl(v___x_1411_, v___x_1412_, v___x_1413_, v___x_1414_, v___x_1426_);
lean_dec_ref(v___x_1426_);
v___x_2551__overap_1428_ = l_panic___redArg(v___x_1408_, v___x_1427_);
v___x_1429_ = lean_apply_1(v___x_2551__overap_1428_, lean_box(0));
lean_dec(v___x_1429_);
v___y_1380_ = v___x_1400_;
v___y_1381_ = v_a_1403_;
goto v___jp_1379_;
}
}
}
else
{
lean_dec(v_a_1403_);
lean_dec_ref(v___f_1366_);
lean_dec_ref(v_out_1321_);
goto v___jp_1324_;
}
}
else
{
lean_object* v_a_1430_; lean_object* v_putStr_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1430_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1402_, 2);
v_putStr_1431_ = lean_ctor_get(v_out_1321_, 4);
lean_inc_ref(v_putStr_1431_);
lean_dec_ref(v_out_1321_);
v___x_1432_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1433_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1434_ = lean_apply_2(v_putStr_1431_, v___x_1432_, lean_box(0));
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
v___y_1368_ = v_a_1430_;
v___y_1369_ = v___y_1390_;
v___y_1370_ = v___x_1400_;
goto v___jp_1367_;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_2556__overap_1453_; lean_object* v___x_1454_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1437_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1438_ = lean_unsigned_to_nat(82u);
v___x_1439_ = lean_unsigned_to_nat(4u);
v___x_1440_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1441_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1442_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1441_, v___x_1343_);
v___x_1443_ = lean_string_append(v___x_1440_, v___x_1442_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1445_ = lean_string_append(v___x_1443_, v___x_1444_);
v___x_1446_ = lean_io_error_to_string(v_a_1435_);
v___x_1447_ = lean_string_append(v___x_1445_, v___x_1446_);
lean_dec_ref(v___x_1446_);
v___x_1448_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1449_ = lean_string_append(v___x_1447_, v___x_1448_);
v___x_1450_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_1451_ = lean_string_append(v___x_1449_, v___x_1450_);
v___x_1452_ = l_mkPanicMessageWithDecl(v___x_1436_, v___x_1437_, v___x_1438_, v___x_1439_, v___x_1451_);
lean_dec_ref(v___x_1451_);
v___x_2556__overap_1453_ = l_panic___redArg(v___x_1433_, v___x_1452_);
v___x_1454_ = lean_apply_1(v___x_2556__overap_1453_, lean_box(0));
lean_dec(v___x_1454_);
v___y_1368_ = v_a_1430_;
v___y_1369_ = v___y_1390_;
v___y_1370_ = v___x_1400_;
goto v___jp_1367_;
}
}
}
}
v___jp_1456_:
{
if (v_verbosity_1340_ == 2)
{
v___y_1390_ = v___x_1343_;
goto v___jp_1389_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = 0;
v___y_1390_ = v___x_1457_;
goto v___jp_1389_;
}
}
v___jp_1458_:
{
lean_object* v_baseName_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_baseName_1460_ = lean_ctor_get(v___x_1363_, 1);
lean_inc(v_baseName_1460_);
v___x_1461_ = l_Lean_Name_toString(v_baseName_1460_, v___y_1459_);
v___x_1462_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
v___x_1464_ = 2;
v___x_1465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*1, v___x_1464_);
v___x_1466_ = lean_apply_2(v_logger_1319_, v___x_1465_, lean_box(0));
goto v___jp_1456_;
}
v___jp_1467_:
{
if (v___y_1468_ == 0)
{
v___y_1459_ = v___y_1468_;
goto v___jp_1458_;
}
else
{
lean_dec_ref(v_logger_1319_);
goto v___jp_1456_;
}
}
}
}
}
else
{
lean_object* v_putStr_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v_outputsRef_x3f_1331_);
lean_dec_ref(v_outputsFile_1322_);
lean_dec_ref(v_bctx_1320_);
lean_dec_ref(v_logger_1319_);
v_putStr_1482_ = lean_ctor_get(v_out_1321_, 4);
lean_inc_ref(v_putStr_1482_);
lean_dec_ref(v_out_1321_);
v___x_1483_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1484_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1485_ = lean_apply_2(v_putStr_1482_, v___x_1483_, lean_box(0));
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
goto v___jp_1328_;
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_2561__overap_1499_; lean_object* v___x_1500_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1488_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1489_ = lean_unsigned_to_nat(82u);
v___x_1490_ = lean_unsigned_to_nat(4u);
v___x_1491_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1492_ = lean_io_error_to_string(v_a_1486_);
v___x_1493_ = lean_string_append(v___x_1491_, v___x_1492_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1495_ = lean_string_append(v___x_1493_, v___x_1494_);
v___x_1496_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
v___x_1498_ = l_mkPanicMessageWithDecl(v___x_1487_, v___x_1488_, v___x_1489_, v___x_1490_, v___x_1497_);
lean_dec_ref(v___x_1497_);
v___x_2561__overap_1499_ = l_panic___redArg(v___x_1484_, v___x_1498_);
v___x_1500_ = lean_apply_1(v___x_2561__overap_1499_, lean_box(0));
lean_dec(v___x_1500_);
goto v___jp_1328_;
}
}
v___jp_1324_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_box(0);
return v___x_1325_;
}
v___jp_1326_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
v___jp_1328_:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___boxed(lean_object* v_logger_1501_, lean_object* v_bctx_1502_, lean_object* v_out_1503_, lean_object* v_outputsFile_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(v_logger_1501_, v_bctx_1502_, v_out_1503_, v_outputsFile_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1508_, lean_object* v_as_1509_, size_t v_i_1510_, size_t v_stop_1511_, lean_object* v_b_1512_){
_start:
{
lean_object* v_val_1515_; uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_eq(v_i_1510_, v_stop_1511_);
if (v___x_1519_ == 0)
{
lean_object* v_putStr_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_putStr_1520_ = lean_ctor_get(v_out_1508_, 4);
v___x_1521_ = lean_array_uget_borrowed(v_as_1509_, v_i_1510_);
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1523_ = lean_string_append(v___x_1522_, v___x_1521_);
v___x_1524_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1525_ = lean_string_append(v___x_1523_, v___x_1524_);
lean_inc_ref(v_putStr_1520_);
lean_inc_ref(v___x_1525_);
v___x_1526_ = lean_apply_2(v_putStr_1520_, v___x_1525_, lean_box(0));
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; 
lean_dec_ref(v___x_1525_);
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_val_1515_ = v_a_1527_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1551_; 
v_a_1528_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1551_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1526_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1551_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1532_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1533_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1534_ = lean_unsigned_to_nat(82u);
v___x_1535_ = lean_unsigned_to_nat(4u);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1538_ = lean_io_error_to_string(v_a_1528_);
v___x_1539_ = lean_string_append(v___x_1537_, v___x_1538_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
v___x_1542_ = l_String_quote(v___x_1525_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 3);
lean_ctor_set(v___x_1530_, 0, v___x_1542_);
v___x_1544_ = v___x_1530_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1545_ = l_Std_Format_defWidth;
v___x_1546_ = l_Std_Format_pretty(v___x_1544_, v___x_1545_, v___x_1536_, v___x_1536_);
v___x_1547_ = lean_string_append(v___x_1541_, v___x_1546_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = l_mkPanicMessageWithDecl(v___x_1532_, v___x_1533_, v___x_1534_, v___x_1535_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1548_);
v_val_1515_ = v___x_1549_;
goto v___jp_1514_;
}
}
}
}
else
{
lean_dec_ref(v_out_1508_);
return v_b_1512_;
}
v___jp_1514_:
{
size_t v___x_1516_; size_t v___x_1517_; 
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1510_, v___x_1516_);
v_i_1510_ = v___x_1517_;
v_b_1512_ = v_val_1515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1552_, lean_object* v_as_1553_, lean_object* v_i_1554_, lean_object* v_stop_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_){
_start:
{
size_t v_i_boxed_1558_; size_t v_stop_boxed_1559_; lean_object* v_res_1560_; 
v_i_boxed_1558_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_stop_boxed_1559_ = lean_unbox_usize(v_stop_1555_);
lean_dec(v_stop_1555_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1552_, v_as_1553_, v_i_boxed_1558_, v_stop_boxed_1559_, v_b_1556_);
lean_dec_ref(v_as_1553_);
return v_res_1560_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1568_ = l_String_quote(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l_Std_Format_defWidth;
v___x_1573_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1574_ = l_Std_Format_pretty(v___x_1573_, v___x_1572_, v___x_1571_, v___x_1571_);
return v___x_1574_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1577_ = l_String_quote(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = l_Std_Format_defWidth;
v___x_1582_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1583_ = l_Std_Format_pretty(v___x_1582_, v___x_1581_, v___x_1580_, v___x_1580_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1584_, lean_object* v_out_1585_, lean_object* v_result_1586_){
_start:
{
uint8_t v___y_1589_; lean_object* v___y_1590_; lean_object* v_failures_1664_; lean_object* v_numJobs_1665_; uint8_t v___y_1667_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_failures_1664_ = lean_ctor_get(v_result_1586_, 0);
lean_inc_ref(v_failures_1664_);
v_numJobs_1665_ = lean_ctor_get(v_result_1586_, 1);
lean_inc(v_numJobs_1665_);
lean_dec_ref(v_result_1586_);
v___x_1700_ = lean_array_get_size(v_failures_1664_);
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = lean_nat_dec_eq(v___x_1700_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v_flush_1703_; lean_object* v_putStr_1704_; lean_object* v___y_1710_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_numJobs_1665_);
v_flush_1703_ = lean_ctor_get(v_out_1585_, 0);
lean_inc_ref(v_flush_1703_);
v_putStr_1704_ = lean_ctor_get(v_out_1585_, 4);
v___x_1721_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1704_);
v___x_1722_ = lean_apply_2(v_putStr_1704_, v___x_1721_, lean_box(0));
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_dec_ref_known(v___x_1722_, 1);
goto v___jp_1711_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1725_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1726_ = lean_unsigned_to_nat(82u);
v___x_1727_ = lean_unsigned_to_nat(4u);
v___x_1728_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1729_ = lean_io_error_to_string(v_a_1723_);
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
v___x_1733_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
v___x_1735_ = l_mkPanicMessageWithDecl(v___x_1724_, v___x_1725_, v___x_1726_, v___x_1727_, v___x_1734_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1735_);
goto v___jp_1711_;
}
v___jp_1705_:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_apply_1(v_flush_1703_, lean_box(0));
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
return v_a_1707_;
}
else
{
lean_object* v___x_1708_; 
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
}
v___jp_1709_:
{
goto v___jp_1705_;
}
v___jp_1711_:
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_nat_dec_lt(v___x_1701_, v___x_1700_);
if (v___x_1712_ == 0)
{
lean_dec_ref(v_failures_1664_);
lean_dec_ref(v_out_1585_);
goto v___jp_1705_;
}
else
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_nat_dec_le(v___x_1700_, v___x_1700_);
if (v___x_1714_ == 0)
{
if (v___x_1712_ == 0)
{
lean_dec_ref(v_failures_1664_);
lean_dec_ref(v_out_1585_);
goto v___jp_1705_;
}
else
{
size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((size_t)0ULL);
v___x_1716_ = lean_usize_of_nat(v___x_1700_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1585_, v_failures_1664_, v___x_1715_, v___x_1716_, v___x_1713_);
lean_dec_ref(v_failures_1664_);
v___y_1710_ = v___x_1717_;
goto v___jp_1709_;
}
}
else
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((size_t)0ULL);
v___x_1719_ = lean_usize_of_nat(v___x_1700_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1585_, v_failures_1664_, v___x_1718_, v___x_1719_, v___x_1713_);
lean_dec_ref(v_failures_1664_);
v___y_1710_ = v___x_1720_;
goto v___jp_1709_;
}
}
}
}
else
{
uint8_t v___x_1737_; 
lean_dec_ref(v_failures_1664_);
v___x_1737_ = l_Lake_BuildConfig_showProgress(v_cfg_1584_);
if (v___x_1737_ == 0)
{
v___y_1667_ = v___x_1737_;
goto v___jp_1666_;
}
else
{
uint8_t v_showSuccess_1738_; 
v_showSuccess_1738_ = lean_ctor_get_uint8(v_cfg_1584_, sizeof(void*)*5 + 5);
v___y_1667_ = v_showSuccess_1738_;
goto v___jp_1666_;
}
}
v___jp_1588_:
{
uint8_t v_noBuild_1591_; 
v_noBuild_1591_ = lean_ctor_get_uint8(v_cfg_1584_, sizeof(void*)*5 + 2);
if (v_noBuild_1591_ == 0)
{
lean_object* v_putStr_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_putStr_1592_ = lean_ctor_get(v_out_1585_, 4);
lean_inc_ref(v_putStr_1592_);
lean_dec_ref(v_out_1585_);
v___x_1593_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1594_ = lean_string_append(v___x_1593_, v___y_1590_);
lean_dec_ref(v___y_1590_);
v___x_1595_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
lean_inc_ref(v___x_1596_);
v___x_1597_ = lean_apply_2(v_putStr_1592_, v___x_1596_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; 
lean_dec_ref(v___x_1596_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
return v_a_1598_;
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1627_; 
v_a_1599_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1601_ = v___x_1597_;
v_isShared_1602_ = v_isSharedCheck_1627_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1597_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1627_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1603_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1604_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1605_ = lean_unsigned_to_nat(82u);
v___x_1606_ = lean_unsigned_to_nat(4u);
v___x_1607_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1609_, v___y_1589_);
v___x_1611_ = lean_string_append(v___x_1607_, v___x_1610_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
v___x_1614_ = lean_io_error_to_string(v_a_1599_);
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1617_ = lean_string_append(v___x_1615_, v___x_1616_);
v___x_1618_ = l_String_quote(v___x_1596_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 3);
lean_ctor_set(v___x_1601_, 0, v___x_1618_);
v___x_1620_ = v___x_1601_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1621_ = l_Std_Format_defWidth;
v___x_1622_ = l_Std_Format_pretty(v___x_1620_, v___x_1621_, v___x_1608_, v___x_1608_);
v___x_1623_ = lean_string_append(v___x_1617_, v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = l_mkPanicMessageWithDecl(v___x_1603_, v___x_1604_, v___x_1605_, v___x_1606_, v___x_1623_);
lean_dec_ref(v___x_1623_);
v___x_1625_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1624_);
return v___x_1625_;
}
}
}
}
else
{
lean_object* v_putStr_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_putStr_1628_ = lean_ctor_get(v_out_1585_, 4);
lean_inc_ref(v_putStr_1628_);
lean_dec_ref(v_out_1585_);
v___x_1629_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1630_ = lean_string_append(v___x_1629_, v___y_1590_);
lean_dec_ref(v___y_1590_);
v___x_1631_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1632_ = lean_string_append(v___x_1630_, v___x_1631_);
lean_inc_ref(v___x_1632_);
v___x_1633_ = lean_apply_2(v_putStr_1628_, v___x_1632_, lean_box(0));
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; 
lean_dec_ref(v___x_1632_);
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
return v_a_1634_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1663_; 
v_a_1635_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1637_ = v___x_1633_;
v_isShared_1638_ = v_isSharedCheck_1663_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1663_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1639_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1640_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1641_ = lean_unsigned_to_nat(82u);
v___x_1642_ = lean_unsigned_to_nat(4u);
v___x_1643_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1646_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1645_, v_noBuild_1591_);
v___x_1647_ = lean_string_append(v___x_1643_, v___x_1646_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_io_error_to_string(v_a_1635_);
v___x_1651_ = lean_string_append(v___x_1649_, v___x_1650_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1653_ = lean_string_append(v___x_1651_, v___x_1652_);
v___x_1654_ = l_String_quote(v___x_1632_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 3);
lean_ctor_set(v___x_1637_, 0, v___x_1654_);
v___x_1656_ = v___x_1637_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1657_ = l_Std_Format_defWidth;
v___x_1658_ = l_Std_Format_pretty(v___x_1656_, v___x_1657_, v___x_1644_, v___x_1644_);
v___x_1659_ = lean_string_append(v___x_1653_, v___x_1658_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = l_mkPanicMessageWithDecl(v___x_1639_, v___x_1640_, v___x_1641_, v___x_1642_, v___x_1659_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1660_);
return v___x_1661_;
}
}
}
}
}
v___jp_1666_:
{
if (v___y_1667_ == 0)
{
lean_object* v___x_1668_; 
lean_dec(v_numJobs_1665_);
lean_dec_ref(v_out_1585_);
v___x_1668_ = lean_box(0);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_nat_dec_eq(v_numJobs_1665_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_dec_eq(v_numJobs_1665_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = l_Nat_reprFast(v_numJobs_1665_);
v___x_1674_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1675_ = lean_string_append(v___x_1673_, v___x_1674_);
v___y_1589_ = v___y_1667_;
v___y_1590_ = v___x_1675_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_numJobs_1665_);
v___x_1676_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1589_ = v___y_1667_;
v___y_1590_ = v___x_1676_;
goto v___jp_1588_;
}
}
else
{
lean_object* v_putStr_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_numJobs_1665_);
v_putStr_1677_ = lean_ctor_get(v_out_1585_, 4);
lean_inc_ref(v_putStr_1677_);
lean_dec_ref(v_out_1585_);
v___x_1678_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1679_ = lean_apply_2(v_putStr_1677_, v___x_1678_, lean_box(0));
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
return v_a_1680_;
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1681_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1682_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1683_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1684_ = lean_unsigned_to_nat(82u);
v___x_1685_ = lean_unsigned_to_nat(4u);
v___x_1686_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1687_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1688_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1687_, v___x_1670_);
v___x_1689_ = lean_string_append(v___x_1686_, v___x_1688_);
lean_dec_ref(v___x_1688_);
v___x_1690_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
v___x_1692_ = lean_io_error_to_string(v_a_1681_);
v___x_1693_ = lean_string_append(v___x_1691_, v___x_1692_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1695_ = lean_string_append(v___x_1693_, v___x_1694_);
v___x_1696_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1682_, v___x_1683_, v___x_1684_, v___x_1685_, v___x_1697_);
lean_dec_ref(v___x_1697_);
v___x_1699_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1698_);
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1739_, lean_object* v_out_1740_, lean_object* v_result_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1739_, v_out_1740_, v_result_1741_);
lean_dec_ref(v_cfg_1739_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(lean_object* v_self_1744_){
_start:
{
lean_object* v_toMonitorResult_1745_; 
v_toMonitorResult_1745_ = lean_ctor_get(v_self_1744_, 0);
lean_inc_ref(v_toMonitorResult_1745_);
return v_toMonitorResult_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0___boxed(lean_object* v_self_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(v_self_1746_);
lean_dec_ref(v_self_1746_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg(){
_start:
{
lean_object* v___f_1750_; 
v___f_1750_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___boxed(lean_object* v___dummy_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg();
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1753_){
_start:
{
lean_object* v___f_1754_; 
v___f_1754_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1754_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1755_){
_start:
{
lean_object* v_out_1756_; 
v_out_1756_ = lean_ctor_get(v_self_1755_, 1);
if (lean_obj_tag(v_out_1756_) == 0)
{
uint8_t v___x_1757_; 
v___x_1757_ = 0;
return v___x_1757_;
}
else
{
uint8_t v___x_1758_; 
v___x_1758_ = 1;
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1759_){
_start:
{
uint8_t v_res_1760_; lean_object* v_r_1761_; 
v_res_1760_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1759_);
lean_dec_ref(v_self_1759_);
v_r_1761_ = lean_box(v_res_1760_);
return v_r_1761_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1762_, lean_object* v_self_1763_){
_start:
{
lean_object* v_out_1764_; 
v_out_1764_ = lean_ctor_get(v_self_1763_, 1);
if (lean_obj_tag(v_out_1764_) == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = 0;
return v___x_1765_;
}
else
{
uint8_t v___x_1766_; 
v___x_1766_ = 1;
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_self_1768_){
_start:
{
uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_res_1769_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1767_, v_self_1768_);
lean_dec_ref(v_self_1768_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1779_, lean_object* v_job_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v_failures_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
lean_inc_ref(v_job_1780_);
v___x_1782_ = l_Lake_Job_toOpaque___redArg(v_job_1780_);
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_mk_empty_array_with_capacity(v___x_1783_);
v___x_1785_ = lean_array_push(v___x_1784_, v___x_1782_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1788_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1789_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1779_, v___x_1785_, v___x_1787_, v___x_1788_);
v_failures_1790_ = lean_ctor_get(v___x_1789_, 0);
v___x_1791_ = lean_array_get_size(v_failures_1790_);
v___x_1792_ = lean_nat_dec_eq(v___x_1791_, v___x_1786_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref(v_job_1780_);
v___x_1793_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1789_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
return v___x_1794_;
}
else
{
lean_object* v_task_1795_; lean_object* v___x_1796_; 
v_task_1795_ = lean_ctor_get(v_job_1780_, 0);
lean_inc_ref(v_task_1795_);
lean_dec_ref(v_job_1780_);
v___x_1796_ = lean_io_wait(v_task_1795_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1805_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v___x_1796_, 1);
lean_dec(v_unused_1806_);
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1797_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1801_);
lean_ctor_set(v___x_1799_, 0, v___x_1789_);
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; lean_object* v_unused_1816_; 
v_unused_1815_ = lean_ctor_get(v___x_1796_, 1);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v___x_1796_, 0);
lean_dec(v_unused_1816_);
v___x_1808_ = v___x_1796_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___x_1796_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 0);
lean_ctor_set(v___x_1808_, 1, v___x_1810_);
lean_ctor_set(v___x_1808_, 0, v___x_1789_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1817_, lean_object* v_job_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1817_, v_job_1818_);
lean_dec_ref(v_ctx_1817_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1821_, lean_object* v_ctx_1822_, lean_object* v_job_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1822_, v_job_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1826_, lean_object* v_ctx_1827_, lean_object* v_job_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1826_, v_ctx_1827_, v_job_1828_);
lean_dec_ref(v_ctx_1827_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object* v_info_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lake_computeTextFileHash(v_info_1833_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_io_metadata(v_info_1833_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1849_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1849_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1849_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_modified_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint64_t v___x_1845_; lean_object* v___x_1847_; 
v_modified_1842_ = lean_ctor_get(v_a_1838_, 1);
lean_inc_ref(v_modified_1842_);
lean_dec(v_a_1838_);
v___x_1843_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1844_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1844_, 0, v_info_1833_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
lean_ctor_set(v___x_1844_, 2, v_modified_1842_);
v___x_1845_ = lean_unbox_uint64(v_a_1836_);
lean_dec(v_a_1836_);
lean_ctor_set_uint64(v___x_1844_, sizeof(void*)*3, v___x_1845_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1844_);
v___x_1847_ = v___x_1840_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1844_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_a_1836_);
lean_dec_ref(v_info_1833_);
v_a_1850_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1837_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1837_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_info_1833_);
v_a_1858_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1835_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1835_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object* v_info_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object* v___x_1872_, lean_object* v_as_1873_, size_t v_sz_1874_, size_t v_i_1875_, lean_object* v_b_1876_){
_start:
{
lean_object* v_a_1879_; uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_lt(v_i_1875_, v_sz_1874_);
if (v___x_1883_ == 0)
{
lean_dec_ref(v___x_1872_);
return v_b_1876_;
}
else
{
lean_object* v_snd_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1907_; 
v_snd_1884_ = lean_ctor_get(v_b_1876_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_b_1876_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v_b_1876_, 0);
lean_dec(v_unused_1908_);
v___x_1886_ = v_b_1876_;
v_isShared_1887_ = v_isSharedCheck_1907_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snd_1884_);
lean_dec(v_b_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1907_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1888_ = lean_box(0);
v_a_1889_ = lean_array_uget_borrowed(v_as_1873_, v_i_1875_);
v___x_1890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0));
lean_inc_ref(v___x_1872_);
v___x_1891_ = l_Lake_joinRelative(v___x_1872_, v___x_1890_);
lean_inc(v_a_1889_);
v___x_1892_ = l_Lake_joinRelative(v___x_1891_, v_a_1889_);
v___x_1893_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v___x_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = l_Lake_BuildTrace_mix(v_snd_1884_, v_a_1894_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_1895_);
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1897_ = v___x_1886_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
v_a_1879_ = v___x_1897_;
goto v___jp_1878_;
}
}
else
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1893_, 1);
if (lean_obj_tag(v_a_1899_) == 11)
{
lean_object* v___x_1901_; 
lean_dec_ref_known(v_a_1899_, 2);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1901_ = v___x_1886_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_snd_1884_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v_a_1879_ = v___x_1901_;
goto v___jp_1878_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
lean_dec(v_a_1899_);
lean_dec_ref(v___x_1872_);
v___x_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1));
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1903_);
v___x_1905_ = v___x_1886_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_snd_1884_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
v___jp_1878_:
{
size_t v___x_1880_; size_t v___x_1881_; 
v___x_1880_ = ((size_t)1ULL);
v___x_1881_ = lean_usize_add(v_i_1875_, v___x_1880_);
v_i_1875_ = v___x_1881_;
v_b_1876_ = v_a_1879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object* v___x_1909_, lean_object* v_as_1910_, lean_object* v_sz_1911_, lean_object* v_i_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_){
_start:
{
size_t v_sz_boxed_1915_; size_t v_i_boxed_1916_; lean_object* v_res_1917_; 
v_sz_boxed_1915_ = lean_unbox_usize(v_sz_1911_);
lean_dec(v_sz_1911_);
v_i_boxed_1916_ = lean_unbox_usize(v_i_1912_);
lean_dec(v_i_1912_);
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1909_, v_as_1910_, v_sz_boxed_1915_, v_i_boxed_1916_, v_b_1913_);
lean_dec_ref(v_as_1910_);
return v_res_1917_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1));
v___x_1921_ = l_Lake_BuildTrace_nil(v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2);
v___x_1937_ = lean_box(0);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1936_);
return v___x_1938_;
}
}
static size_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1939_; size_t v_sz_1940_; 
v___x_1939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v_sz_1940_ = lean_array_size(v___x_1939_);
return v_sz_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t v_sz_1941_, size_t v_i_1942_, lean_object* v_bs_1943_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_lt(v_i_1942_, v_sz_1941_);
if (v___x_1945_ == 0)
{
return v_bs_1943_;
}
else
{
lean_object* v_v_1946_; lean_object* v_config_1947_; lean_object* v_dir_1948_; uint8_t v_bootstrap_1949_; lean_object* v_buildDir_1950_; lean_object* v___x_1951_; lean_object* v_bs_x27_1952_; lean_object* v_val_1954_; 
v_v_1946_ = lean_array_uget_borrowed(v_bs_1943_, v_i_1942_);
v_config_1947_ = lean_ctor_get(v_v_1946_, 6);
v_dir_1948_ = lean_ctor_get(v_v_1946_, 4);
lean_inc_ref(v_dir_1948_);
v_bootstrap_1949_ = lean_ctor_get_uint8(v_config_1947_, sizeof(void*)*28);
v_buildDir_1950_ = lean_ctor_get(v_config_1947_, 5);
lean_inc_ref(v_buildDir_1950_);
v___x_1951_ = lean_unsigned_to_nat(0u);
v_bs_x27_1952_ = lean_array_uset(v_bs_1943_, v_i_1942_, v___x_1951_);
if (v_bootstrap_1949_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v_buildDir_1950_);
lean_dec_ref(v_dir_1948_);
v___x_1959_ = lean_box(0);
v_val_1954_ = v___x_1959_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; size_t v_sz_1966_; size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v_fst_1969_; 
v___x_1960_ = l_System_FilePath_normalize(v_buildDir_1950_);
v___x_1961_ = l_Lake_joinRelative(v_dir_1948_, v___x_1960_);
v___x_1962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0));
v___x_1963_ = l_Lake_joinRelative(v___x_1961_, v___x_1962_);
v___x_1964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v___x_1965_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8);
v_sz_1966_ = lean_usize_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9);
v___x_1967_ = ((size_t)0ULL);
lean_inc_ref(v___x_1963_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1963_, v___x_1964_, v_sz_1966_, v___x_1967_, v___x_1965_);
v_fst_1969_ = lean_ctor_get(v___x_1968_, 0);
if (lean_obj_tag(v_fst_1969_) == 0)
{
lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v_snd_1970_ = lean_ctor_get(v___x_1968_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1968_, 0);
lean_dec(v_unused_1979_);
v___x_1972_ = v___x_1968_;
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_dec(v___x_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1963_);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_snd_1970_);
v___x_1975_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
v_val_1954_ = v___x_1976_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_val_1980_; 
lean_inc_ref(v_fst_1969_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v___x_1963_);
v_val_1980_ = lean_ctor_get(v_fst_1969_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v_fst_1969_, 1);
v_val_1954_ = v_val_1980_;
goto v___jp_1953_;
}
}
v___jp_1953_:
{
size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1942_, v___x_1955_);
v___x_1957_ = lean_array_uset(v_bs_x27_1952_, v_i_1942_, v_val_1954_);
v_i_1942_ = v___x_1956_;
v_bs_1943_ = v___x_1957_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object* v_sz_1981_, lean_object* v_i_1982_, lean_object* v_bs_1983_, lean_object* v___y_1984_){
_start:
{
size_t v_sz_boxed_1985_; size_t v_i_boxed_1986_; lean_object* v_res_1987_; 
v_sz_boxed_1985_ = lean_unbox_usize(v_sz_1981_);
lean_dec(v_sz_1981_);
v_i_boxed_1986_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_boxed_1985_, v_i_boxed_1986_, v_bs_1983_);
return v_res_1987_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = l_Lean_versionStringCore;
v___x_1990_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0));
v___x_1991_ = lean_string_append(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2));
v___x_1994_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1);
v___x_1995_ = lean_string_append(v___x_1994_, v___x_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_nat_to_int(v___x_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5(void){
_start:
{
uint32_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = 0;
v___x_1999_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4);
v___x_2000_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set_uint32(v___x_2000_, sizeof(void*)*1, v___x_1998_);
return v___x_2000_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_unsigned_to_nat(16u);
v___x_2003_ = lean_mk_array(v___x_2002_, v___x_2001_);
return v___x_2003_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object* v_ws_2009_, lean_object* v_cfg_2010_, lean_object* v_jobs_2011_, lean_object* v_cancelTk_x3f_2012_){
_start:
{
uint8_t v___y_2015_; uint8_t v___y_2016_; uint8_t v___y_2017_; uint8_t v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v___y_2024_; uint8_t v___y_2025_; lean_object* v_val_2026_; uint8_t v___y_2044_; uint8_t v___y_2045_; uint8_t v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; uint8_t v___y_2053_; uint8_t v___y_2054_; lean_object* v_val_2057_; uint8_t v___x_2083_; 
v___x_2083_ = l_System_Platform_isOSX;
if (v___x_2083_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_2084_; 
v_macosxDeploymentTarget_x3f_2084_ = lean_ctor_get(v_cfg_2010_, 4);
lean_inc(v_macosxDeploymentTarget_x3f_2084_);
v_val_2057_ = v_macosxDeploymentTarget_x3f_2084_;
goto v___jp_2056_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_2085_; 
v_macosxDeploymentTarget_x3f_2085_ = lean_ctor_get(v_cfg_2010_, 4);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_2085_) == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___y_2089_; 
v___x_2086_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8));
v___x_2087_ = lean_io_getenv(v___x_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9));
v___y_2089_ = v___x_2091_;
goto v___jp_2088_;
}
else
{
lean_object* v_val_2092_; 
v_val_2092_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2092_);
lean_dec_ref_known(v___x_2087_, 1);
v___y_2089_ = v_val_2092_;
goto v___jp_2088_;
}
v___jp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___y_2089_);
v_val_2057_ = v___x_2090_;
goto v___jp_2056_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_2085_);
v_val_2057_ = v_macosxDeploymentTarget_x3f_2085_;
goto v___jp_2056_;
}
}
v___jp_2014_:
{
lean_object* v_lakeEnv_2027_; lean_object* v_packages_2028_; size_t v_sz_2029_; size_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint64_t v___x_2034_; uint64_t v___x_2035_; uint64_t v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_lakeEnv_2027_ = lean_ctor_get(v_ws_2009_, 0);
v_packages_2028_ = lean_ctor_get(v_ws_2009_, 4);
v_sz_2029_ = lean_array_size(v_packages_2028_);
v___x_2030_ = ((size_t)0ULL);
lean_inc_ref(v_packages_2028_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_2029_, v___x_2030_, v_packages_2028_);
v___x_2032_ = lean_alloc_ctor(0, 5, 6);
lean_ctor_set(v___x_2032_, 0, v___y_2023_);
lean_ctor_set(v___x_2032_, 1, v___y_2020_);
lean_ctor_set(v___x_2032_, 2, v___y_2022_);
lean_ctor_set(v___x_2032_, 3, v___y_2019_);
lean_ctor_set(v___x_2032_, 4, v___y_2021_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*5, v___y_2017_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*5 + 1, v___y_2016_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*5 + 2, v___y_2015_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*5 + 3, v___y_2018_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*5 + 4, v___y_2025_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*5 + 5, v___y_2024_);
v___x_2033_ = l_Lake_Env_leanGithash(v_lakeEnv_2027_);
v___x_2034_ = l_Lake_Hash_nil;
v___x_2035_ = lean_string_hash(v___x_2033_);
v___x_2036_ = lean_uint64_mix_hash(v___x_2034_, v___x_2035_);
v___x_2037_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3);
v___x_2038_ = lean_string_append(v___x_2037_, v___x_2033_);
lean_dec_ref(v___x_2033_);
v___x_2039_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_2040_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5);
v___x_2041_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
lean_ctor_set(v___x_2041_, 1, v___x_2039_);
lean_ctor_set(v___x_2041_, 2, v___x_2040_);
lean_ctor_set_uint64(v___x_2041_, sizeof(void*)*3, v___x_2036_);
v___x_2042_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2032_);
lean_ctor_set(v___x_2042_, 1, v_ws_2009_);
lean_ctor_set(v___x_2042_, 2, v___x_2041_);
lean_ctor_set(v___x_2042_, 3, v___x_2031_);
lean_ctor_set(v___x_2042_, 4, v_jobs_2011_);
lean_ctor_set(v___x_2042_, 5, v_val_2026_);
lean_ctor_set(v___x_2042_, 6, v_cancelTk_x3f_2012_);
return v___x_2042_;
}
v___jp_2043_:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_box(0);
v___y_2015_ = v___y_2046_;
v___y_2016_ = v___y_2045_;
v___y_2017_ = v___y_2044_;
v___y_2018_ = v___y_2047_;
v___y_2019_ = v___y_2048_;
v___y_2020_ = v___y_2049_;
v___y_2021_ = v___y_2050_;
v___y_2022_ = v___y_2051_;
v___y_2023_ = v___y_2052_;
v___y_2024_ = v___y_2053_;
v___y_2025_ = v___y_2054_;
v_val_2026_ = v___x_2055_;
goto v___jp_2014_;
}
v___jp_2056_:
{
lean_object* v_outputsFile_x3f_2058_; 
v_outputsFile_x3f_2058_ = lean_ctor_get(v_cfg_2010_, 1);
lean_inc(v_outputsFile_x3f_2058_);
if (lean_obj_tag(v_outputsFile_x3f_2058_) == 0)
{
lean_object* v_toLogConfig_2059_; uint8_t v_oldMode_2060_; uint8_t v_trustHash_2061_; uint8_t v_noBuild_2062_; uint8_t v_failFast_2063_; uint8_t v_verbosity_2064_; uint8_t v_showSuccess_2065_; lean_object* v_outputsIdx_2066_; lean_object* v_leanOptOverrides_2067_; 
v_toLogConfig_2059_ = lean_ctor_get(v_cfg_2010_, 0);
lean_inc_ref(v_toLogConfig_2059_);
v_oldMode_2060_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5);
v_trustHash_2061_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 1);
v_noBuild_2062_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 2);
v_failFast_2063_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 3);
v_verbosity_2064_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 4);
v_showSuccess_2065_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 5);
v_outputsIdx_2066_ = lean_ctor_get(v_cfg_2010_, 2);
lean_inc(v_outputsIdx_2066_);
v_leanOptOverrides_2067_ = lean_ctor_get(v_cfg_2010_, 3);
lean_inc(v_leanOptOverrides_2067_);
lean_dec_ref(v_cfg_2010_);
v___y_2044_ = v_oldMode_2060_;
v___y_2045_ = v_trustHash_2061_;
v___y_2046_ = v_noBuild_2062_;
v___y_2047_ = v_failFast_2063_;
v___y_2048_ = v_leanOptOverrides_2067_;
v___y_2049_ = v_outputsFile_x3f_2058_;
v___y_2050_ = v_val_2057_;
v___y_2051_ = v_outputsIdx_2066_;
v___y_2052_ = v_toLogConfig_2059_;
v___y_2053_ = v_showSuccess_2065_;
v___y_2054_ = v_verbosity_2064_;
goto v___jp_2043_;
}
else
{
lean_object* v_toLogConfig_2068_; uint8_t v_oldMode_2069_; uint8_t v_trustHash_2070_; uint8_t v_noBuild_2071_; uint8_t v_failFast_2072_; uint8_t v_verbosity_2073_; uint8_t v_showSuccess_2074_; lean_object* v_outputsIdx_2075_; lean_object* v_leanOptOverrides_2076_; lean_object* v_packages_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v_toLogConfig_2068_ = lean_ctor_get(v_cfg_2010_, 0);
lean_inc_ref(v_toLogConfig_2068_);
v_oldMode_2069_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5);
v_trustHash_2070_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 1);
v_noBuild_2071_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 2);
v_failFast_2072_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 3);
v_verbosity_2073_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 4);
v_showSuccess_2074_ = lean_ctor_get_uint8(v_cfg_2010_, sizeof(void*)*5 + 5);
v_outputsIdx_2075_ = lean_ctor_get(v_cfg_2010_, 2);
lean_inc(v_outputsIdx_2075_);
v_leanOptOverrides_2076_ = lean_ctor_get(v_cfg_2010_, 3);
lean_inc(v_leanOptOverrides_2076_);
lean_dec_ref(v_cfg_2010_);
v_packages_2077_ = lean_ctor_get(v_ws_2009_, 4);
v___x_2078_ = lean_array_get_size(v_packages_2077_);
v___x_2079_ = lean_nat_dec_lt(v_outputsIdx_2075_, v___x_2078_);
if (v___x_2079_ == 0)
{
v___y_2044_ = v_oldMode_2069_;
v___y_2045_ = v_trustHash_2070_;
v___y_2046_ = v_noBuild_2071_;
v___y_2047_ = v_failFast_2072_;
v___y_2048_ = v_leanOptOverrides_2076_;
v___y_2049_ = v_outputsFile_x3f_2058_;
v___y_2050_ = v_val_2057_;
v___y_2051_ = v_outputsIdx_2075_;
v___y_2052_ = v_toLogConfig_2068_;
v___y_2053_ = v_showSuccess_2074_;
v___y_2054_ = v_verbosity_2073_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7);
v___x_2081_ = lean_st_mk_ref(v___x_2080_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___y_2015_ = v_noBuild_2071_;
v___y_2016_ = v_trustHash_2070_;
v___y_2017_ = v_oldMode_2069_;
v___y_2018_ = v_failFast_2072_;
v___y_2019_ = v_leanOptOverrides_2076_;
v___y_2020_ = v_outputsFile_x3f_2058_;
v___y_2021_ = v_val_2057_;
v___y_2022_ = v_outputsIdx_2075_;
v___y_2023_ = v_toLogConfig_2068_;
v___y_2024_ = v_showSuccess_2074_;
v___y_2025_ = v_verbosity_2073_;
v_val_2026_ = v___x_2082_;
goto v___jp_2014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object* v_ws_2093_, lean_object* v_cfg_2094_, lean_object* v_jobs_2095_, lean_object* v_cancelTk_x3f_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2093_, v_cfg_2094_, v_jobs_2095_, v_cancelTk_x3f_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_log_2107_; uint8_t v_action_2108_; uint8_t v_wantsRebuild_2109_; uint8_t v_canceled_2110_; lean_object* v_trace_2111_; lean_object* v_buildTime_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2141_; 
v_log_2107_ = lean_ctor_get(v___y_2105_, 0);
v_action_2108_ = lean_ctor_get_uint8(v___y_2105_, sizeof(void*)*3);
v_wantsRebuild_2109_ = lean_ctor_get_uint8(v___y_2105_, sizeof(void*)*3 + 1);
v_canceled_2110_ = lean_ctor_get_uint8(v___y_2105_, sizeof(void*)*3 + 2);
v_trace_2111_ = lean_ctor_get(v___y_2105_, 1);
v_buildTime_2112_ = lean_ctor_get(v___y_2105_, 2);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___y_2105_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2114_ = v___y_2105_;
v_isShared_2115_ = v_isSharedCheck_2141_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_buildTime_2112_);
lean_inc(v_trace_2111_);
lean_inc(v_log_2107_);
lean_dec(v___y_2105_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2141_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_apply_7(v_build_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v_log_2107_, lean_box(0));
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_a_2118_ = lean_ctor_get(v___x_2116_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2120_ = v___x_2116_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_a_2118_);
v___x_2123_ = v___x_2114_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2118_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_trace_2111_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_buildTime_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*3, v_action_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*3 + 1, v_wantsRebuild_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*3 + 2, v_canceled_2110_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2123_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2117_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2140_; 
v_a_2129_ = lean_ctor_get(v___x_2116_, 0);
v_a_2130_ = lean_ctor_get(v___x_2116_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2132_ = v___x_2116_;
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_inc(v_a_2129_);
lean_dec(v___x_2116_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_a_2130_);
v___x_2135_ = v___x_2114_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2130_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_trace_2111_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_buildTime_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2139_, sizeof(void*)*3, v_action_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2139_, sizeof(void*)*3 + 1, v_wantsRebuild_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2139_, sizeof(void*)*3 + 2, v_canceled_2110_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v___x_2135_);
v___x_2137_ = v___x_2132_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2129_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_2152_, lean_object* v_build_2153_, lean_object* v_caption_2154_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___f_2156_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2156_, 0, v_build_2153_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_box(1);
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_st_mk_ref(v___x_2160_);
v___x_2163_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_2164_ = l_Lake_Job_async___redArg(v___x_2157_, v___f_2156_, v___x_2158_, v_caption_2154_, v___x_2163_, v___x_2161_, v___x_2159_, v___x_2162_, v_bctx_2152_);
v___x_2165_ = lean_st_ref_get(v___x_2162_);
lean_dec(v___x_2162_);
lean_dec(v___x_2165_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_2166_, lean_object* v_build_2167_, lean_object* v_caption_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2166_, v_build_2167_, v_caption_2168_);
lean_dec_ref(v_bctx_2166_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_2171_, lean_object* v_bctx_2172_, lean_object* v_build_2173_, lean_object* v_caption_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2172_, v_build_2173_, v_caption_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_bctx_2178_, lean_object* v_build_2179_, lean_object* v_caption_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_2177_, v_bctx_2178_, v_build_2179_, v_caption_2180_);
lean_dec_ref(v_bctx_2178_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_2183_, uint8_t v___x_2184_, uint8_t v___x_2185_, lean_object* v_as_2186_, size_t v_i_2187_, size_t v_stop_2188_, lean_object* v_b_2189_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = lean_usize_dec_eq(v_i_2187_, v_stop_2188_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; 
v___x_2192_ = lean_array_uget_borrowed(v_as_2186_, v_i_2187_);
lean_inc_ref(v___x_2183_);
v___x_2193_ = l_Lake_logToStream(v___x_2192_, v___x_2183_, v___x_2184_, v___x_2185_);
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2187_, v___x_2194_);
v_i_2187_ = v___x_2195_;
v_b_2189_ = v___x_2193_;
goto _start;
}
else
{
lean_dec_ref(v___x_2183_);
return v_b_2189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_2197_, lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v_as_2200_, lean_object* v_i_2201_, lean_object* v_stop_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v___x_1088__boxed_2205_; uint8_t v___x_1089__boxed_2206_; size_t v_i_boxed_2207_; size_t v_stop_boxed_2208_; lean_object* v_res_2209_; 
v___x_1088__boxed_2205_ = lean_unbox(v___x_2198_);
v___x_1089__boxed_2206_ = lean_unbox(v___x_2199_);
v_i_boxed_2207_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_stop_boxed_2208_ = lean_unbox_usize(v_stop_2202_);
lean_dec(v_stop_2202_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2197_, v___x_1088__boxed_2205_, v___x_1089__boxed_2206_, v_as_2200_, v_i_boxed_2207_, v_stop_boxed_2208_, v_b_2203_);
lean_dec_ref(v_as_2200_);
return v_res_2209_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v___x_2210_, lean_object* v___x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
if (lean_obj_tag(v_x_2212_) == 0)
{
if (lean_obj_tag(v_x_2213_) == 0)
{
uint8_t v___x_2214_; 
v___x_2214_ = 1;
return v___x_2214_;
}
else
{
uint8_t v___x_2215_; 
v___x_2215_ = 0;
return v___x_2215_;
}
}
else
{
if (lean_obj_tag(v_x_2213_) == 0)
{
uint8_t v___x_2216_; 
v___x_2216_ = 0;
return v___x_2216_;
}
else
{
lean_object* v_val_2217_; uint8_t v___x_2218_; 
v_val_2217_ = lean_ctor_get(v_x_2213_, 0);
v___x_2218_ = lean_unbox(v_val_2217_);
if (v___x_2218_ == 0)
{
lean_object* v_val_2219_; uint8_t v___x_2220_; 
v_val_2219_ = lean_ctor_get(v_x_2212_, 0);
v___x_2220_ = lean_unbox(v_val_2219_);
if (v___x_2220_ == 0)
{
uint8_t v___x_2221_; 
v___x_2221_ = lean_nat_dec_lt(v___x_2210_, v___x_2211_);
return v___x_2221_;
}
else
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_unbox(v_val_2217_);
return v___x_2222_;
}
}
else
{
lean_object* v_val_2223_; uint8_t v___x_2224_; 
v_val_2223_ = lean_ctor_get(v_x_2212_, 0);
v___x_2224_ = lean_unbox(v_val_2223_);
return v___x_2224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v___x_2225_, lean_object* v___x_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
uint8_t v_res_2229_; lean_object* v_r_2230_; 
v_res_2229_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_2225_, v___x_2226_, v_x_2227_, v_x_2228_);
lean_dec(v_x_2228_);
lean_dec(v_x_2227_);
lean_dec(v___x_2226_);
lean_dec(v___x_2225_);
v_r_2230_ = lean_box(v_res_2229_);
return v_r_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_2231_, uint8_t v___x_2232_, uint8_t v___x_2233_, lean_object* v_bctx_2234_, lean_object* v_out_2235_, lean_object* v_outputsFile_2236_){
_start:
{
lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2252_; lean_object* v_outputsRef_x3f_2264_; 
v_outputsRef_x3f_2264_ = lean_ctor_get(v_bctx_2234_, 5);
lean_inc(v_outputsRef_x3f_2264_);
if (lean_obj_tag(v_outputsRef_x3f_2264_) == 1)
{
lean_object* v_toContext_2265_; lean_object* v_toBuildConfig_2266_; lean_object* v_val_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2384_; 
v_toContext_2265_ = lean_ctor_get(v_bctx_2234_, 1);
lean_inc(v_toContext_2265_);
v_toBuildConfig_2266_ = lean_ctor_get(v_bctx_2234_, 0);
lean_inc_ref(v_toBuildConfig_2266_);
lean_dec_ref(v_bctx_2234_);
v_val_2267_ = lean_ctor_get(v_outputsRef_x3f_2264_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_outputsRef_x3f_2264_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2269_ = v_outputsRef_x3f_2264_;
v_isShared_2270_ = v_isSharedCheck_2384_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_val_2267_);
lean_dec(v_outputsRef_x3f_2264_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2384_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_lakeEnv_2271_; lean_object* v_packages_2272_; uint8_t v_verbosity_2273_; lean_object* v_outputsIdx_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_lakeEnv_2271_ = lean_ctor_get(v_toContext_2265_, 0);
lean_inc_ref(v_lakeEnv_2271_);
v_packages_2272_ = lean_ctor_get(v_toContext_2265_, 4);
lean_inc_ref(v_packages_2272_);
lean_dec(v_toContext_2265_);
v_verbosity_2273_ = lean_ctor_get_uint8(v_toBuildConfig_2266_, sizeof(void*)*5 + 4);
v_outputsIdx_2274_ = lean_ctor_get(v_toBuildConfig_2266_, 2);
lean_inc(v_outputsIdx_2274_);
lean_dec_ref(v_toBuildConfig_2266_);
v___x_2275_ = lean_array_get_size(v_packages_2272_);
v___x_2276_ = lean_nat_dec_lt(v_outputsIdx_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v_putStr_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec(v_outputsIdx_2274_);
lean_dec_ref(v_packages_2272_);
lean_dec_ref(v_lakeEnv_2271_);
lean_del_object(v___x_2269_);
lean_dec(v_val_2267_);
lean_dec_ref(v_outputsFile_2236_);
lean_dec_ref(v___x_2231_);
v_putStr_2277_ = lean_ctor_get(v_out_2235_, 4);
lean_inc_ref(v_putStr_2277_);
lean_dec_ref(v_out_2235_);
v___x_2278_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_2279_ = lean_apply_2(v_putStr_2277_, v___x_2278_, lean_box(0));
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref_known(v___x_2279_, 1);
goto v___jp_2260_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2282_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2283_ = lean_unsigned_to_nat(82u);
v___x_2284_ = lean_unsigned_to_nat(4u);
v___x_2285_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2286_ = lean_io_error_to_string(v_a_2280_);
v___x_2287_ = lean_string_append(v___x_2285_, v___x_2286_);
lean_dec_ref(v___x_2286_);
v___x_2288_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2289_ = lean_string_append(v___x_2287_, v___x_2288_);
v___x_2290_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_2291_ = lean_string_append(v___x_2289_, v___x_2290_);
v___x_2292_ = l_mkPanicMessageWithDecl(v___x_2281_, v___x_2282_, v___x_2283_, v___x_2284_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2292_);
goto v___jp_2260_;
}
}
else
{
lean_object* v___x_2294_; uint8_t v___y_2296_; uint8_t v___y_2360_; uint8_t v___y_2369_; lean_object* v_config_2370_; lean_object* v_enableArtifactCache_x3f_2371_; 
v___x_2294_ = lean_array_fget(v_packages_2272_, v_outputsIdx_2274_);
v_config_2370_ = lean_ctor_get(v___x_2294_, 6);
v_enableArtifactCache_x3f_2371_ = lean_ctor_get(v_config_2370_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_2371_) == 0)
{
lean_object* v_enableArtifactCache_x3f_2372_; 
v_enableArtifactCache_x3f_2372_ = lean_ctor_get(v_lakeEnv_2271_, 6);
lean_inc(v_enableArtifactCache_x3f_2372_);
lean_dec_ref(v_lakeEnv_2271_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2372_) == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_config_2375_; lean_object* v_enableArtifactCache_x3f_2376_; 
v___x_2373_ = lean_unsigned_to_nat(0u);
v___x_2374_ = lean_array_fget(v_packages_2272_, v___x_2373_);
lean_dec_ref(v_packages_2272_);
v_config_2375_ = lean_ctor_get(v___x_2374_, 6);
lean_inc_ref(v_config_2375_);
lean_dec(v___x_2374_);
v_enableArtifactCache_x3f_2376_ = lean_ctor_get(v_config_2375_, 24);
lean_inc(v_enableArtifactCache_x3f_2376_);
lean_dec_ref(v_config_2375_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2376_) == 0)
{
uint8_t v___x_2377_; 
v___x_2377_ = 0;
v___y_2360_ = v___x_2377_;
goto v___jp_2359_;
}
else
{
lean_object* v_val_2378_; uint8_t v___x_2379_; 
v_val_2378_ = lean_ctor_get(v_enableArtifactCache_x3f_2376_, 0);
lean_inc(v_val_2378_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2376_, 1);
v___x_2379_ = lean_unbox(v_val_2378_);
lean_dec(v_val_2378_);
v___y_2369_ = v___x_2379_;
goto v___jp_2368_;
}
}
else
{
lean_object* v_val_2380_; uint8_t v___x_2381_; 
lean_dec_ref(v_packages_2272_);
v_val_2380_ = lean_ctor_get(v_enableArtifactCache_x3f_2372_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2372_, 1);
v___x_2381_ = lean_unbox(v_val_2380_);
lean_dec(v_val_2380_);
v___y_2369_ = v___x_2381_;
goto v___jp_2368_;
}
}
else
{
lean_object* v_val_2382_; uint8_t v___x_2383_; 
lean_dec_ref(v_packages_2272_);
lean_dec_ref(v_lakeEnv_2271_);
v_val_2382_ = lean_ctor_get(v_enableArtifactCache_x3f_2371_, 0);
v___x_2383_ = lean_unbox(v_val_2382_);
v___y_2369_ = v___x_2383_;
goto v___jp_2368_;
}
v___jp_2295_:
{
lean_object* v___x_2297_; lean_object* v_config_2298_; lean_object* v_toLeanConfig_2299_; lean_object* v_platformIndependent_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2297_ = lean_st_ref_get(v_val_2267_);
lean_dec(v_val_2267_);
v_config_2298_ = lean_ctor_get(v___x_2294_, 6);
lean_inc_ref(v_config_2298_);
lean_dec(v___x_2294_);
v_toLeanConfig_2299_ = lean_ctor_get(v_config_2298_, 1);
lean_inc_ref(v_toLeanConfig_2299_);
lean_dec_ref(v_config_2298_);
v_platformIndependent_2300_ = lean_ctor_get(v_toLeanConfig_2299_, 10);
lean_inc(v_platformIndependent_2300_);
lean_dec_ref(v_toLeanConfig_2299_);
v___x_2301_ = lean_box(v___x_2276_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2301_);
v___x_2303_ = v___x_2269_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2304_ = l_instBEqOption_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_outputsIdx_2274_, v___x_2275_, v_platformIndependent_2300_, v___x_2303_);
lean_dec_ref(v___x_2303_);
lean_dec(v_platformIndependent_2300_);
lean_dec(v_outputsIdx_2274_);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_2307_ = l_Lake_CacheMap_writeFile(v_outputsFile_2236_, v___x_2297_, v___x_2304_, v___x_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 2);
v___x_2309_ = lean_array_get_size(v_a_2308_);
v___x_2310_ = lean_nat_dec_eq(v___x_2309_, v___x_2305_);
if (v___x_2310_ == 0)
{
if (v___y_2296_ == 0)
{
lean_dec(v_a_2308_);
lean_dec_ref(v_out_2235_);
lean_dec_ref(v___x_2231_);
goto v___jp_2238_;
}
else
{
lean_object* v_putStr_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_putStr_2311_ = lean_ctor_get(v_out_2235_, 4);
lean_inc_ref(v_putStr_2311_);
lean_dec_ref(v_out_2235_);
v___x_2312_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_2313_ = lean_apply_2(v_putStr_2311_, v___x_2312_, lean_box(0));
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref_known(v___x_2313_, 1);
v___y_2241_ = v___x_2305_;
v___y_2242_ = v_a_2308_;
goto v___jp_2240_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2316_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2317_ = lean_unsigned_to_nat(82u);
v___x_2318_ = lean_unsigned_to_nat(4u);
v___x_2319_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2320_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2320_, v___y_2296_);
v___x_2322_ = lean_string_append(v___x_2319_, v___x_2321_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2324_ = lean_string_append(v___x_2322_, v___x_2323_);
v___x_2325_ = lean_io_error_to_string(v_a_2314_);
v___x_2326_ = lean_string_append(v___x_2324_, v___x_2325_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2328_ = lean_string_append(v___x_2326_, v___x_2327_);
v___x_2329_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
v___x_2331_ = l_mkPanicMessageWithDecl(v___x_2315_, v___x_2316_, v___x_2317_, v___x_2318_, v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2331_);
v___y_2241_ = v___x_2305_;
v___y_2242_ = v_a_2308_;
goto v___jp_2240_;
}
}
}
else
{
lean_dec(v_a_2308_);
lean_dec_ref(v_out_2235_);
lean_dec_ref(v___x_2231_);
goto v___jp_2238_;
}
}
else
{
lean_object* v_a_2333_; lean_object* v_putStr_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_a_2333_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2307_, 2);
v_putStr_2334_ = lean_ctor_get(v_out_2235_, 4);
lean_inc_ref(v_putStr_2334_);
lean_dec_ref(v_out_2235_);
v___x_2335_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_2336_ = lean_apply_2(v_putStr_2334_, v___x_2335_, lean_box(0));
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_dec_ref_known(v___x_2336_, 1);
v___y_2250_ = v___x_2305_;
v___y_2251_ = v_a_2333_;
v___y_2252_ = v___y_2296_;
goto v___jp_2249_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2339_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2340_ = lean_unsigned_to_nat(82u);
v___x_2341_ = lean_unsigned_to_nat(4u);
v___x_2342_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2343_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2343_, v___x_2276_);
v___x_2345_ = lean_string_append(v___x_2342_, v___x_2344_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
v___x_2348_ = lean_io_error_to_string(v_a_2337_);
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2351_ = lean_string_append(v___x_2349_, v___x_2350_);
v___x_2352_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_2353_ = lean_string_append(v___x_2351_, v___x_2352_);
v___x_2354_ = l_mkPanicMessageWithDecl(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2341_, v___x_2353_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2354_);
v___y_2250_ = v___x_2305_;
v___y_2251_ = v_a_2333_;
v___y_2252_ = v___y_2296_;
goto v___jp_2249_;
}
}
}
}
v___jp_2357_:
{
if (v_verbosity_2273_ == 2)
{
v___y_2296_ = v___x_2276_;
goto v___jp_2295_;
}
else
{
uint8_t v___x_2358_; 
v___x_2358_ = 0;
v___y_2296_ = v___x_2358_;
goto v___jp_2295_;
}
}
v___jp_2359_:
{
lean_object* v_baseName_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_baseName_2361_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_baseName_2361_);
v___x_2362_ = l_Lean_Name_toString(v_baseName_2361_, v___y_2360_);
v___x_2363_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
v___x_2365_ = 2;
v___x_2366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set_uint8(v___x_2366_, sizeof(void*)*1, v___x_2365_);
lean_inc_ref(v___x_2231_);
v___x_2367_ = l_Lake_logToStream(v___x_2366_, v___x_2231_, v___x_2232_, v___x_2233_);
lean_dec_ref_known(v___x_2366_, 1);
goto v___jp_2357_;
}
v___jp_2368_:
{
if (v___y_2369_ == 0)
{
v___y_2360_ = v___y_2369_;
goto v___jp_2359_;
}
else
{
goto v___jp_2357_;
}
}
}
}
}
else
{
lean_object* v_putStr_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec(v_outputsRef_x3f_2264_);
lean_dec_ref(v_outputsFile_2236_);
lean_dec_ref(v_bctx_2234_);
lean_dec_ref(v___x_2231_);
v_putStr_2385_ = lean_ctor_get(v_out_2235_, 4);
lean_inc_ref(v_putStr_2385_);
lean_dec_ref(v_out_2235_);
v___x_2386_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_2387_ = lean_apply_2(v_putStr_2385_, v___x_2386_, lean_box(0));
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_dec_ref_known(v___x_2387_, 1);
goto v___jp_2262_;
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2390_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2391_ = lean_unsigned_to_nat(82u);
v___x_2392_ = lean_unsigned_to_nat(4u);
v___x_2393_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2394_ = lean_io_error_to_string(v_a_2388_);
v___x_2395_ = lean_string_append(v___x_2393_, v___x_2394_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2397_ = lean_string_append(v___x_2395_, v___x_2396_);
v___x_2398_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_2399_ = lean_string_append(v___x_2397_, v___x_2398_);
v___x_2400_ = l_mkPanicMessageWithDecl(v___x_2389_, v___x_2390_, v___x_2391_, v___x_2392_, v___x_2399_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2400_);
goto v___jp_2262_;
}
}
v___jp_2238_:
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_box(0);
return v___x_2239_;
}
v___jp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2243_ = lean_array_get_size(v___y_2242_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_nat_dec_lt(v___y_2241_, v___x_2243_);
if (v___x_2245_ == 0)
{
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___x_2231_);
return v___x_2244_;
}
else
{
size_t v___x_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = ((size_t)0ULL);
v___x_2247_ = lean_usize_of_nat(v___x_2243_);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2231_, v___x_2232_, v___x_2233_, v___y_2242_, v___x_2246_, v___x_2247_, v___x_2244_);
lean_dec_ref(v___y_2242_);
return v___x_2248_;
}
}
v___jp_2249_:
{
if (v___y_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___x_2231_);
v___x_2253_ = lean_box(0);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2254_ = lean_array_get_size(v___y_2251_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_nat_dec_lt(v___y_2250_, v___x_2254_);
if (v___x_2256_ == 0)
{
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___x_2231_);
return v___x_2255_;
}
else
{
size_t v___x_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = ((size_t)0ULL);
v___x_2258_ = lean_usize_of_nat(v___x_2254_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2231_, v___x_2232_, v___x_2233_, v___y_2251_, v___x_2257_, v___x_2258_, v___x_2255_);
lean_dec_ref(v___y_2251_);
return v___x_2259_;
}
}
}
v___jp_2260_:
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_box(0);
return v___x_2261_;
}
v___jp_2262_:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_box(0);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v___x_2404_, lean_object* v_bctx_2405_, lean_object* v_out_2406_, lean_object* v_outputsFile_2407_, lean_object* v_a_2408_){
_start:
{
uint8_t v___x_1332__boxed_2409_; uint8_t v___x_1333__boxed_2410_; lean_object* v_res_2411_; 
v___x_1332__boxed_2409_ = lean_unbox(v___x_2403_);
v___x_1333__boxed_2410_ = lean_unbox(v___x_2404_);
v_res_2411_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2402_, v___x_1332__boxed_2409_, v___x_1333__boxed_2410_, v_bctx_2405_, v_out_2406_, v_outputsFile_2407_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2412_, lean_object* v_bctx_2413_, lean_object* v_mctx_2414_, lean_object* v_result_2415_){
_start:
{
lean_object* v___y_2418_; lean_object* v_out_2421_; uint8_t v_outLv_2422_; uint8_t v_useAnsi_2423_; lean_object* v_toMonitorResult_2424_; lean_object* v_out_2425_; lean_object* v___x_2441_; lean_object* v_outputsFile_x3f_2442_; 
v_out_2421_ = lean_ctor_get(v_mctx_2414_, 1);
lean_inc_ref_n(v_out_2421_, 2);
v_outLv_2422_ = lean_ctor_get_uint8(v_mctx_2414_, sizeof(void*)*4);
v_useAnsi_2423_ = lean_ctor_get_uint8(v_mctx_2414_, sizeof(void*)*4 + 4);
lean_dec_ref(v_mctx_2414_);
v_toMonitorResult_2424_ = lean_ctor_get(v_result_2415_, 0);
lean_inc_ref_n(v_toMonitorResult_2424_, 2);
v_out_2425_ = lean_ctor_get(v_result_2415_, 1);
lean_inc_ref(v_out_2425_);
lean_dec_ref(v_result_2415_);
v___x_2441_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2412_, v_out_2421_, v_toMonitorResult_2424_);
v_outputsFile_x3f_2442_ = lean_ctor_get(v_cfg_2412_, 1);
if (lean_obj_tag(v_outputsFile_x3f_2442_) == 1)
{
lean_object* v_val_2443_; lean_object* v___x_2444_; 
v_val_2443_ = lean_ctor_get(v_outputsFile_x3f_2442_, 0);
lean_inc(v_val_2443_);
lean_inc_ref(v_out_2421_);
v___x_2444_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2421_, v_outLv_2422_, v_useAnsi_2423_, v_bctx_2413_, v_out_2421_, v_val_2443_);
goto v___jp_2426_;
}
else
{
lean_dec_ref(v_out_2421_);
lean_dec_ref(v_bctx_2413_);
goto v___jp_2426_;
}
v___jp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_mk_io_user_error(v___y_2418_);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
v___jp_2426_:
{
if (lean_obj_tag(v_out_2425_) == 0)
{
uint8_t v_noBuild_2427_; 
v_noBuild_2427_ = lean_ctor_get_uint8(v_cfg_2412_, sizeof(void*)*5 + 2);
lean_dec_ref(v_cfg_2412_);
if (v_noBuild_2427_ == 0)
{
lean_object* v_a_2428_; 
lean_dec_ref(v_toMonitorResult_2424_);
v_a_2428_ = lean_ctor_get(v_out_2425_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v_out_2425_, 1);
v___y_2418_ = v_a_2428_;
goto v___jp_2417_;
}
else
{
uint8_t v_wantsRebuild_2429_; 
v_wantsRebuild_2429_ = lean_ctor_get_uint8(v_toMonitorResult_2424_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2424_);
if (v_wantsRebuild_2429_ == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v_out_2425_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v_out_2425_, 1);
v___y_2418_ = v_a_2430_;
goto v___jp_2417_;
}
else
{
uint8_t v___x_2431_; lean_object* v___x_2432_; 
lean_dec_ref_known(v_out_2425_, 1);
v___x_2431_ = 3;
v___x_2432_ = lean_io_exit(v___x_2431_);
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v_toMonitorResult_2424_);
lean_dec_ref(v_cfg_2412_);
v_a_2433_ = lean_ctor_get(v_out_2425_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_out_2425_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v_out_2425_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v_out_2425_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 0);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2445_, lean_object* v_bctx_2446_, lean_object* v_mctx_2447_, lean_object* v_result_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2445_, v_bctx_2446_, v_mctx_2447_, v_result_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2451_, lean_object* v_cfg_2452_, lean_object* v_bctx_2453_, lean_object* v_mctx_2454_, lean_object* v_result_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2452_, v_bctx_2453_, v_mctx_2454_, v_result_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_cfg_2459_, lean_object* v_bctx_2460_, lean_object* v_mctx_2461_, lean_object* v_result_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2458_, v_cfg_2459_, v_bctx_2460_, v_mctx_2461_, v_result_2462_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2465_, lean_object* v_build_2466_, lean_object* v_cfg_2467_, lean_object* v_caption_2468_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_cancelTk_x3f_2473_; uint8_t v_failFast_2479_; 
v___x_2470_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2471_ = lean_st_mk_ref(v___x_2470_);
v_failFast_2479_ = lean_ctor_get_uint8(v_cfg_2467_, sizeof(void*)*5 + 3);
if (v_failFast_2479_ == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_box(0);
v_cancelTk_x3f_2473_ = v___x_2480_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = l_IO_CancelToken_new();
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
v_cancelTk_x3f_2473_ = v___x_2482_;
goto v___jp_2472_;
}
v___jp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_inc(v_cancelTk_x3f_2473_);
lean_inc(v___x_2471_);
v___x_2474_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2467_, v___x_2471_, v_cancelTk_x3f_2473_);
lean_inc_ref(v_cfg_2467_);
v___x_2475_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2465_, v_cfg_2467_, v___x_2471_, v_cancelTk_x3f_2473_);
v___x_2476_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2475_, v_build_2466_, v_caption_2468_);
v___x_2477_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2474_, v___x_2476_);
v___x_2478_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2467_, v___x_2475_, v___x_2474_, v___x_2477_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2483_, lean_object* v_build_2484_, lean_object* v_cfg_2485_, lean_object* v_caption_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2483_, v_build_2484_, v_cfg_2485_, v_caption_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2489_, lean_object* v_ws_2490_, lean_object* v_build_2491_, lean_object* v_cfg_2492_, lean_object* v_caption_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2490_, v_build_2491_, v_cfg_2492_, v_caption_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2496_, lean_object* v_ws_2497_, lean_object* v_build_2498_, lean_object* v_cfg_2499_, lean_object* v_caption_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2496_, v_ws_2497_, v_build_2498_, v_cfg_2499_, v_caption_2500_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2506_, lean_object* v_job_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v_out_2510_; 
v___x_2509_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2506_, v_job_2507_);
v_out_2510_ = lean_ctor_get(v___x_2509_, 1);
lean_inc_ref(v_out_2510_);
if (lean_obj_tag(v_out_2510_) == 0)
{
lean_object* v_toMonitorResult_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2526_; 
v_toMonitorResult_2511_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2509_, 1);
lean_dec(v_unused_2527_);
v___x_2513_ = v___x_2509_;
v_isShared_2514_ = v_isSharedCheck_2526_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_toMonitorResult_2511_);
lean_dec(v___x_2509_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2526_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2525_; 
v_a_2515_ = lean_ctor_get(v_out_2510_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_out_2510_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2517_ = v_out_2510_;
v_isShared_2518_ = v_isSharedCheck_2525_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v_out_2510_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2525_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 1, v___x_2520_);
v___x_2522_ = v___x_2513_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_toMonitorResult_2511_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2551_; 
v_a_2528_ = lean_ctor_get(v_out_2510_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_out_2510_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2530_ = v_out_2510_;
v_isShared_2531_ = v_isSharedCheck_2551_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v_out_2510_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2551_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v_toMonitorResult_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2549_; 
v_toMonitorResult_2532_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2509_, 1);
lean_dec(v_unused_2550_);
v___x_2534_ = v___x_2509_;
v_isShared_2535_ = v_isSharedCheck_2549_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_toMonitorResult_2532_);
lean_dec(v___x_2509_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2549_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_task_2536_; lean_object* v___x_2537_; 
v_task_2536_ = lean_ctor_get(v_a_2528_, 0);
lean_inc_ref(v_task_2536_);
lean_dec(v_a_2528_);
v___x_2537_ = lean_io_wait(v_task_2536_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2537_, 2);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v_a_2538_);
v___x_2540_ = v___x_2530_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2540_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___x_2540_);
v___x_2542_ = v___x_2534_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_toMonitorResult_2532_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_dec_ref_known(v___x_2537_, 2);
lean_del_object(v___x_2530_);
v___x_2545_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___x_2545_);
v___x_2547_ = v___x_2534_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_toMonitorResult_2532_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2552_, lean_object* v_job_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2552_, v_job_2553_);
lean_dec_ref(v_mctx_2552_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2556_, lean_object* v_mctx_2557_, lean_object* v_job_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2557_, v_job_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2561_, lean_object* v_mctx_2562_, lean_object* v_job_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2561_, v_mctx_2562_, v_job_2563_);
lean_dec_ref(v_mctx_2562_);
return v_res_2565_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2580_, lean_object* v_build_2581_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_out_2594_; 
v___x_2583_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2584_ = lean_st_mk_ref(v___x_2583_);
v___x_2585_ = 0;
v___x_2586_ = 1;
v___x_2587_ = lean_box(0);
v___x_2588_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2584_);
v___x_2589_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2588_, v___x_2584_, v___x_2587_);
v___x_2590_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2580_, v___x_2588_, v___x_2584_, v___x_2587_);
v___x_2591_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2592_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2590_, v_build_2581_, v___x_2591_);
lean_dec_ref(v___x_2590_);
v___x_2593_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2589_, v___x_2592_);
lean_dec_ref(v___x_2589_);
v_out_2594_ = lean_ctor_get(v___x_2593_, 1);
lean_inc_ref(v_out_2594_);
lean_dec_ref(v___x_2593_);
if (lean_obj_tag(v_out_2594_) == 0)
{
lean_dec_ref_known(v_out_2594_, 1);
return v___x_2585_;
}
else
{
lean_dec_ref_known(v_out_2594_, 1);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2595_, lean_object* v_build_2596_, lean_object* v_a_2597_){
_start:
{
uint8_t v_res_2598_; lean_object* v_r_2599_; 
v_res_2598_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2595_, v_build_2596_);
v_r_2599_ = lean_box(v_res_2598_);
return v_r_2599_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2600_, lean_object* v_ws_2601_, lean_object* v_build_2602_){
_start:
{
uint8_t v___x_2604_; 
v___x_2604_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2601_, v_build_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2605_, lean_object* v_ws_2606_, lean_object* v_build_2607_, lean_object* v_a_2608_){
_start:
{
uint8_t v_res_2609_; lean_object* v_r_2610_; 
v_res_2609_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2605_, v_ws_2606_, v_build_2607_);
v_r_2610_ = lean_box(v_res_2609_);
return v_r_2610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2611_, lean_object* v_build_2612_, lean_object* v_cfg_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v_cancelTk_x3f_2618_; uint8_t v_failFast_2625_; 
v___x_2615_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2616_ = lean_st_mk_ref(v___x_2615_);
v_failFast_2625_ = lean_ctor_get_uint8(v_cfg_2613_, sizeof(void*)*5 + 3);
if (v_failFast_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_box(0);
v_cancelTk_x3f_2618_ = v___x_2626_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = l_IO_CancelToken_new();
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v_cancelTk_x3f_2618_ = v___x_2628_;
goto v___jp_2617_;
}
v___jp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_inc(v_cancelTk_x3f_2618_);
lean_inc(v___x_2616_);
v___x_2619_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2613_, v___x_2616_, v_cancelTk_x3f_2618_);
lean_inc_ref(v_cfg_2613_);
v___x_2620_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2611_, v_cfg_2613_, v___x_2616_, v_cancelTk_x3f_2618_);
v___x_2621_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2622_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2620_, v_build_2612_, v___x_2621_);
v___x_2623_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2619_, v___x_2622_);
v___x_2624_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2613_, v___x_2620_, v___x_2619_, v___x_2623_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2629_, lean_object* v_build_2630_, lean_object* v_cfg_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lake_Workspace_runBuild___redArg(v_ws_2629_, v_build_2630_, v_cfg_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2634_, lean_object* v_ws_2635_, lean_object* v_build_2636_, lean_object* v_cfg_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lake_Workspace_runBuild___redArg(v_ws_2635_, v_build_2636_, v_cfg_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_ws_2641_, lean_object* v_build_2642_, lean_object* v_cfg_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lake_Workspace_runBuild(v_00_u03b1_2640_, v_ws_2641_, v_build_2642_, v_cfg_2643_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2646_, lean_object* v_cfg_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; 
lean_inc(v_a_2648_);
v___x_2650_ = l_Lake_Workspace_runBuild___redArg(v_a_2648_, v_build_2646_, v_cfg_2647_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2651_, lean_object* v_cfg_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lake_runBuild___redArg(v_build_2651_, v_cfg_2652_, v_a_2653_);
lean_dec(v_a_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2656_, lean_object* v_build_2657_, lean_object* v_cfg_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
lean_inc(v_a_2659_);
v___x_2661_ = l_Lake_Workspace_runBuild___redArg(v_a_2659_, v_build_2657_, v_cfg_2658_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_build_2663_, lean_object* v_cfg_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lake_runBuild(v_00_u03b1_2662_, v_build_2663_, v_cfg_2664_, v_a_2665_);
lean_dec(v_a_2665_);
return v_res_2667_;
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
