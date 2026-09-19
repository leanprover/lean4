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
lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
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
uint8_t lean_uint32_to_uint8(uint32_t);
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
uint8_t l_Lake_instOrdJobAction_ord(uint8_t, uint8_t);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
uint32_t l_Lake_LogLevel_icon(uint8_t);
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
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_228_; lean_object* v___x_7489__overap_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_7489__overap_229_ = lean_panic_fn_borrowed(v___x_228_, v_msg_226_);
v___x_230_ = lean_apply_1(v___x_7489__overap_229_, lean_box(0));
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
uint8_t v___y_13776__boxed_423_; uint8_t v_useAnsi_13777__boxed_424_; size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v___y_13776__boxed_423_ = lean_unbox(v___y_415_);
v_useAnsi_13777__boxed_424_ = lean_unbox(v_useAnsi_416_);
v_i_boxed_425_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_414_, v___y_13776__boxed_423_, v_useAnsi_13777__boxed_424_, v_as_417_, v_i_boxed_425_, v_stop_boxed_426_, v_b_420_, v___y_421_);
lean_dec_ref(v_as_417_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_444_; lean_object* v_val_445_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_jobNo_455_; lean_object* v_totalJobs_456_; uint8_t v_wantsRebuild_457_; lean_object* v_failures_458_; lean_object* v_resetCtrl_459_; lean_object* v_lastUpdate_460_; lean_object* v_spinnerIdx_461_; lean_object* v_out_462_; uint8_t v_outLv_463_; uint8_t v_failLv_464_; uint8_t v_minAction_465_; uint8_t v_showOptional_466_; uint8_t v_useAnsi_467_; uint8_t v_showProgress_468_; uint8_t v_showTime_469_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___y_476_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; lean_object* v_task_568_; lean_object* v_caption_569_; uint8_t v_optional_570_; lean_object* v___y_572_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; uint32_t v___y_576_; uint8_t v___y_577_; uint8_t v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; lean_object* v___y_607_; lean_object* v___y_608_; uint8_t v___y_609_; lean_object* v___y_610_; uint32_t v___y_611_; uint8_t v___y_612_; uint8_t v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; uint32_t v___y_624_; uint8_t v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; uint32_t v___y_652_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint8_t v___y_664_; uint8_t v___y_665_; lean_object* v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; uint8_t v___y_679_; uint8_t v___y_680_; uint8_t v___y_681_; uint8_t v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; uint8_t v___y_689_; uint8_t v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; uint8_t v___y_710_; uint8_t v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; uint8_t v___y_717_; uint8_t v___y_718_; uint8_t v___y_734_; lean_object* v___y_735_; uint8_t v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; uint8_t v___y_740_; uint8_t v___y_741_; lean_object* v___y_746_; lean_object* v___x_757_; lean_object* v_a_758_; 
v_jobNo_455_ = lean_ctor_get(v_a_437_, 0);
lean_inc(v_jobNo_455_);
v_totalJobs_456_ = lean_ctor_get(v_a_437_, 1);
lean_inc(v_totalJobs_456_);
v_wantsRebuild_457_ = lean_ctor_get_uint8(v_a_437_, sizeof(void*)*6);
v_failures_458_ = lean_ctor_get(v_a_437_, 2);
v_resetCtrl_459_ = lean_ctor_get(v_a_437_, 3);
v_lastUpdate_460_ = lean_ctor_get(v_a_437_, 4);
v_spinnerIdx_461_ = lean_ctor_get(v_a_437_, 5);
v_out_462_ = lean_ctor_get(v_a_436_, 1);
v_outLv_463_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4);
v_failLv_464_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4 + 1);
v_minAction_465_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4 + 2);
v_showOptional_466_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4 + 3);
v_useAnsi_467_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4 + 4);
v_showProgress_468_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4 + 5);
v_showTime_469_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*4 + 6);
v_task_568_ = lean_ctor_get(v_job_435_, 0);
lean_inc_ref(v_task_568_);
v_caption_569_ = lean_ctor_get(v_job_435_, 2);
lean_inc_ref(v_caption_569_);
v_optional_570_ = lean_ctor_get_uint8(v_job_435_, sizeof(void*)*3);
lean_dec_ref(v_job_435_);
v___x_757_ = lean_task_get_own(v_task_568_);
v_a_758_ = lean_ctor_get(v___x_757_, 1);
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___y_746_ = v_a_758_;
goto v___jp_745_;
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___y_440_);
return v___x_442_;
}
v___jp_443_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_val_445_);
lean_ctor_set(v___x_446_, 1, v___y_444_);
return v___x_446_;
}
v___jp_447_:
{
lean_object* v_out_450_; lean_object* v_flush_451_; lean_object* v___x_452_; 
v_out_450_ = lean_ctor_get(v___y_448_, 1);
v_flush_451_ = lean_ctor_get(v_out_450_, 0);
lean_inc_ref(v_flush_451_);
v___x_452_ = lean_apply_1(v_flush_451_, lean_box(0));
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___y_444_ = v___y_449_;
v_val_445_ = v_a_453_;
goto v___jp_443_;
}
else
{
lean_object* v___x_454_; 
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = lean_box(0);
v___y_444_ = v___y_449_;
v_val_445_ = v___x_454_;
goto v___jp_443_;
}
}
v___jp_470_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_lt(v___y_473_, v___y_475_);
lean_dec(v___y_473_);
if (v___x_477_ == 0)
{
lean_dec(v___y_475_);
lean_dec_ref(v___y_472_);
v___y_448_ = v___y_471_;
v___y_449_ = v___y_474_;
goto v___jp_447_;
}
else
{
lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v_snd_482_; 
v___x_478_ = lean_box(0);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___y_475_);
lean_dec(v___y_475_);
lean_inc_ref(v_out_462_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_462_, v___y_476_, v_useAnsi_467_, v___y_472_, v___x_479_, v___x_480_, v___x_478_, v___y_474_);
lean_dec_ref(v___y_472_);
v_snd_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_snd_482_);
lean_dec_ref(v___x_481_);
v___y_448_ = v___y_471_;
v___y_449_ = v_snd_482_;
goto v___jp_447_;
}
}
v___jp_483_:
{
if (v___y_488_ == 0)
{
lean_dec(v___y_489_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
v___y_448_ = v___y_484_;
v___y_449_ = v___y_487_;
goto v___jp_447_;
}
else
{
if (v___y_490_ == 0)
{
v___y_471_ = v___y_484_;
v___y_472_ = v___y_485_;
v___y_473_ = v___y_486_;
v___y_474_ = v___y_487_;
v___y_475_ = v___y_489_;
v___y_476_ = v_outLv_463_;
goto v___jp_470_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = 0;
v___y_471_ = v___y_484_;
v___y_472_ = v___y_485_;
v___y_473_ = v___y_486_;
v___y_474_ = v___y_487_;
v___y_475_ = v___y_489_;
v___y_476_ = v___x_491_;
goto v___jp_470_;
}
}
}
v___jp_492_:
{
lean_object* v_out_502_; lean_object* v_jobNo_503_; lean_object* v_totalJobs_504_; uint8_t v_wantsRebuild_505_; lean_object* v_failures_506_; lean_object* v_resetCtrl_507_; lean_object* v_lastUpdate_508_; lean_object* v_spinnerIdx_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_555_; 
v_out_502_ = lean_ctor_get(v___y_493_, 1);
v_jobNo_503_ = lean_ctor_get(v___y_499_, 0);
v_totalJobs_504_ = lean_ctor_get(v___y_499_, 1);
v_wantsRebuild_505_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*6);
v_failures_506_ = lean_ctor_get(v___y_499_, 2);
v_resetCtrl_507_ = lean_ctor_get(v___y_499_, 3);
v_lastUpdate_508_ = lean_ctor_get(v___y_499_, 4);
v_spinnerIdx_509_ = lean_ctor_get(v___y_499_, 5);
v_isSharedCheck_555_ = !lean_is_exclusive(v___y_499_);
if (v_isSharedCheck_555_ == 0)
{
v___x_511_ = v___y_499_;
v_isShared_512_ = v_isSharedCheck_555_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_spinnerIdx_509_);
lean_inc(v_lastUpdate_508_);
lean_inc(v_resetCtrl_507_);
lean_inc(v_failures_506_);
lean_inc(v_totalJobs_504_);
lean_inc(v_jobNo_503_);
lean_dec(v___y_499_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_555_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_putStr_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v_putStr_513_ = lean_ctor_get(v_out_502_, 4);
v___x_514_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 3, v___x_514_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_jobNo_503_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_totalJobs_504_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_failures_506_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_lastUpdate_508_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_spinnerIdx_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*6, v_wantsRebuild_505_);
v___x_516_ = v_reuseFailAlloc_554_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_string_append(v_resetCtrl_507_, v___y_501_);
lean_dec_ref(v___y_501_);
v___x_518_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_519_ = lean_string_append(v___x_517_, v___x_518_);
lean_inc_ref(v_putStr_513_);
lean_inc_ref(v___x_519_);
v___x_520_ = lean_apply_2(v_putStr_513_, v___x_519_, lean_box(0));
if (lean_obj_tag(v___x_520_) == 0)
{
lean_dec_ref_known(v___x_520_, 1);
lean_dec_ref(v___x_519_);
v___y_484_ = v___y_493_;
v___y_485_ = v___y_494_;
v___y_486_ = v___y_495_;
v___y_487_ = v___x_516_;
v___y_488_ = v___y_496_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_500_;
goto v___jp_483_;
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_553_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_553_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_553_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_553_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_525_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_526_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_527_ = lean_unsigned_to_nat(82u);
v___x_528_ = lean_unsigned_to_nat(4u);
v___x_529_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_530_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc(v___y_495_);
v___x_532_ = l_Lean_Name_num___override(v___x_531_, v___y_495_);
v___x_533_ = l_Lean_Name_str___override(v___x_532_, v___x_530_);
v___x_534_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_535_ = l_Lean_Name_str___override(v___x_533_, v___x_534_);
v___x_536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_535_, v___y_498_);
v___x_537_ = lean_string_append(v___x_529_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = lean_io_error_to_string(v_a_521_);
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
lean_dec_ref(v___x_540_);
v___x_542_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
v___x_544_ = l_String_quote(v___x_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 3);
lean_ctor_set(v___x_523_, 0, v___x_544_);
v___x_546_ = v___x_523_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_552_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = l_Std_Format_defWidth;
lean_inc_n(v___y_495_, 2);
v___x_548_ = l_Std_Format_pretty(v___x_546_, v___x_547_, v___y_495_, v___y_495_);
v___x_549_ = lean_string_append(v___x_543_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_mkPanicMessageWithDecl(v___x_525_, v___x_526_, v___x_527_, v___x_528_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_550_);
v___y_484_ = v___y_493_;
v___y_485_ = v___y_494_;
v___y_486_ = v___y_495_;
v___y_487_ = v___x_516_;
v___y_488_ = v___y_496_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_500_;
goto v___jp_483_;
}
}
}
}
}
}
v___jp_556_:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lake_Ansi_chalk(v___y_566_, v___y_564_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_566_);
v___y_493_ = v___y_557_;
v___y_494_ = v___y_558_;
v___y_495_ = v___y_559_;
v___y_496_ = v___y_560_;
v___y_497_ = v___y_561_;
v___y_498_ = v___y_563_;
v___y_499_ = v___y_562_;
v___y_500_ = v___y_565_;
v___y_501_ = v___x_567_;
goto v___jp_492_;
}
v___jp_571_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_586_ = lean_string_push(v___x_585_, v___y_576_);
v___x_587_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
v___x_589_ = l_Nat_reprFast(v_jobNo_455_);
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = l_Nat_reprFast(v_totalJobs_456_);
v___x_594_ = lean_string_append(v___x_592_, v___x_593_);
lean_dec_ref(v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
v___x_597_ = lean_string_append(v___x_596_, v___y_573_);
v___x_598_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = lean_string_append(v___x_599_, v___y_579_);
lean_dec_ref(v___y_579_);
v___x_601_ = lean_string_append(v___x_600_, v___x_598_);
v___x_602_ = lean_string_append(v___x_601_, v_caption_569_);
lean_dec_ref(v_caption_569_);
v___x_603_ = lean_string_append(v___x_602_, v___y_584_);
lean_dec_ref(v___y_584_);
if (v_useAnsi_467_ == 0)
{
v___y_493_ = v___y_572_;
v___y_494_ = v___y_580_;
v___y_495_ = v___y_575_;
v___y_496_ = v___y_577_;
v___y_497_ = v___y_581_;
v___y_498_ = v___y_578_;
v___y_499_ = v___y_582_;
v___y_500_ = v___y_583_;
v___y_501_ = v___x_603_;
goto v___jp_492_;
}
else
{
if (v___y_577_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_557_ = v___y_572_;
v___y_558_ = v___y_580_;
v___y_559_ = v___y_575_;
v___y_560_ = v___y_577_;
v___y_561_ = v___y_581_;
v___y_562_ = v___y_582_;
v___y_563_ = v___y_578_;
v___y_564_ = v___x_603_;
v___y_565_ = v___y_583_;
v___y_566_ = v___x_604_;
goto v___jp_556_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = l_Lake_LogLevel_ansiColor(v___y_574_);
v___y_557_ = v___y_572_;
v___y_558_ = v___y_580_;
v___y_559_ = v___y_575_;
v___y_560_ = v___y_577_;
v___y_561_ = v___y_581_;
v___y_562_ = v___y_582_;
v___y_563_ = v___y_578_;
v___y_564_ = v___x_603_;
v___y_565_ = v___y_583_;
v___y_566_ = v___x_605_;
goto v___jp_556_;
}
}
}
v___jp_606_:
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_572_ = v___y_607_;
v___y_573_ = v___y_608_;
v___y_574_ = v___y_609_;
v___y_575_ = v___y_610_;
v___y_576_ = v___y_611_;
v___y_577_ = v___y_612_;
v___y_578_ = v___y_613_;
v___y_579_ = v___y_614_;
v___y_580_ = v___y_615_;
v___y_581_ = v___y_616_;
v___y_582_ = v___y_617_;
v___y_583_ = v___y_618_;
v___y_584_ = v___x_619_;
goto v___jp_571_;
}
v___jp_620_:
{
if (v_showTime_469_ == 0)
{
lean_dec(v___y_629_);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_633_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_623_;
v___y_611_ = v___y_624_;
v___y_612_ = v___y_625_;
v___y_613_ = v___y_626_;
v___y_614_ = v___y_627_;
v___y_615_ = v___y_628_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
goto v___jp_606_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v___y_623_, v___y_629_);
if (v___x_634_ == 0)
{
lean_dec(v___y_629_);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_633_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_623_;
v___y_611_ = v___y_624_;
v___y_612_ = v___y_625_;
v___y_613_ = v___y_626_;
v___y_614_ = v___y_627_;
v___y_615_ = v___y_628_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
goto v___jp_606_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_636_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_629_);
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___y_572_ = v___y_621_;
v___y_573_ = v___y_633_;
v___y_574_ = v___y_622_;
v___y_575_ = v___y_623_;
v___y_576_ = v___y_624_;
v___y_577_ = v___y_625_;
v___y_578_ = v___y_626_;
v___y_579_ = v___y_627_;
v___y_580_ = v___y_628_;
v___y_581_ = v___y_630_;
v___y_582_ = v___y_631_;
v___y_583_ = v___y_632_;
v___y_584_ = v___x_639_;
goto v___jp_571_;
}
}
}
v___jp_640_:
{
if (v_optional_570_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_621_ = v___y_641_;
v___y_622_ = v___y_642_;
v___y_623_ = v___y_645_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_646_;
v___y_626_ = v___y_649_;
v___y_627_ = v___y_651_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_647_;
v___y_631_ = v___y_648_;
v___y_632_ = v___y_650_;
v___y_633_ = v___x_653_;
goto v___jp_620_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_621_ = v___y_641_;
v___y_622_ = v___y_642_;
v___y_623_ = v___y_645_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_646_;
v___y_626_ = v___y_649_;
v___y_627_ = v___y_651_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_647_;
v___y_631_ = v___y_648_;
v___y_632_ = v___y_650_;
v___y_633_ = v___x_654_;
goto v___jp_620_;
}
}
v___jp_655_:
{
if (v___y_661_ == 0)
{
if (v_showProgress_468_ == 0)
{
lean_dec(v___y_662_);
lean_dec(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_663_;
goto v___jp_439_;
}
else
{
if (v_useAnsi_467_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = l_Lake_instOrdJobAction_ord(v_minAction_465_, v___y_665_);
if (v___x_666_ == 2)
{
lean_dec(v___y_662_);
lean_dec(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_663_;
goto v___jp_439_;
}
else
{
lean_object* v___x_667_; uint32_t v___x_668_; 
v___x_667_ = l_Lake_JobAction_verb(v___y_664_, v___y_665_);
v___x_668_ = 10004;
v___y_641_ = v___y_656_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_658_;
v___y_644_ = v___y_660_;
v___y_645_ = v___y_659_;
v___y_646_ = v___y_661_;
v___y_647_ = v___y_662_;
v___y_648_ = v___y_663_;
v___y_649_ = v_showProgress_468_;
v___y_650_ = v___y_664_;
v___y_651_ = v___x_667_;
v___y_652_ = v___x_668_;
goto v___jp_640_;
}
}
else
{
lean_dec(v___y_662_);
lean_dec(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_663_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v___x_669_; uint32_t v___x_670_; 
v___x_669_ = l_Lake_JobAction_verb(v___y_664_, v___y_665_);
v___x_670_ = l_Lake_LogLevel_icon(v___y_657_);
v___y_641_ = v___y_656_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_658_;
v___y_644_ = v___y_660_;
v___y_645_ = v___y_659_;
v___y_646_ = v___y_661_;
v___y_647_ = v___y_662_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_661_;
v___y_650_ = v___y_664_;
v___y_651_ = v___x_669_;
v___y_652_ = v___x_670_;
goto v___jp_640_;
}
}
v___jp_671_:
{
if (v_optional_570_ == 0)
{
v___y_656_ = v___y_672_;
v___y_657_ = v___y_673_;
v___y_658_ = v___y_674_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_676_;
v___y_661_ = v___y_681_;
v___y_662_ = v___y_677_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_679_;
v___y_665_ = v___y_680_;
goto v___jp_655_;
}
else
{
if (v_showOptional_466_ == 0)
{
lean_dec(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_678_;
goto v___jp_439_;
}
else
{
v___y_656_ = v___y_672_;
v___y_657_ = v___y_673_;
v___y_658_ = v___y_674_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_676_;
v___y_661_ = v___y_681_;
v___y_662_ = v___y_677_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_679_;
v___y_665_ = v___y_680_;
goto v___jp_655_;
}
}
}
v___jp_682_:
{
if (v___y_690_ == 0)
{
if (v___y_687_ == 0)
{
v___y_672_ = v___y_691_;
v___y_673_ = v___y_683_;
v___y_674_ = v___y_684_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___y_688_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_690_;
v___y_680_ = v___y_689_;
v___y_681_ = v___y_687_;
goto v___jp_671_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = l_Lake_instOrdLogLevel_ord(v_outLv_463_, v___y_683_);
if (v___x_693_ == 2)
{
v___y_672_ = v___y_691_;
v___y_673_ = v___y_683_;
v___y_674_ = v___y_684_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___y_688_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_690_;
v___y_680_ = v___y_689_;
v___y_681_ = v___y_690_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___y_691_;
v___y_673_ = v___y_683_;
v___y_674_ = v___y_684_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___y_688_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_690_;
v___y_680_ = v___y_689_;
v___y_681_ = v___y_687_;
goto v___jp_671_;
}
}
}
else
{
if (v_optional_570_ == 0)
{
lean_object* v_jobNo_694_; lean_object* v_totalJobs_695_; uint8_t v_wantsRebuild_696_; lean_object* v_failures_697_; lean_object* v_resetCtrl_698_; lean_object* v_lastUpdate_699_; lean_object* v_spinnerIdx_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_jobNo_694_ = lean_ctor_get(v___y_692_, 0);
v_totalJobs_695_ = lean_ctor_get(v___y_692_, 1);
v_wantsRebuild_696_ = lean_ctor_get_uint8(v___y_692_, sizeof(void*)*6);
v_failures_697_ = lean_ctor_get(v___y_692_, 2);
v_resetCtrl_698_ = lean_ctor_get(v___y_692_, 3);
v_lastUpdate_699_ = lean_ctor_get(v___y_692_, 4);
v_spinnerIdx_700_ = lean_ctor_get(v___y_692_, 5);
v_isSharedCheck_708_ = !lean_is_exclusive(v___y_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v___y_692_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_spinnerIdx_700_);
lean_inc(v_lastUpdate_699_);
lean_inc(v_resetCtrl_698_);
lean_inc(v_failures_697_);
lean_inc(v_totalJobs_695_);
lean_inc(v_jobNo_694_);
lean_dec(v___y_692_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
lean_inc_ref(v_caption_569_);
v___x_704_ = lean_array_push(v_failures_697_, v_caption_569_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 2, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_jobNo_694_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_totalJobs_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_resetCtrl_698_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_lastUpdate_699_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_spinnerIdx_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*6, v_wantsRebuild_696_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v___y_672_ = v___y_691_;
v___y_673_ = v___y_683_;
v___y_674_ = v___y_684_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___y_688_;
v___y_678_ = v___x_706_;
v___y_679_ = v___y_690_;
v___y_680_ = v___y_689_;
v___y_681_ = v___y_690_;
goto v___jp_671_;
}
}
}
else
{
v___y_672_ = v___y_691_;
v___y_673_ = v___y_683_;
v___y_674_ = v___y_684_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_685_;
v___y_677_ = v___y_688_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_690_;
v___y_680_ = v___y_689_;
v___y_681_ = v___y_690_;
goto v___jp_671_;
}
}
}
v___jp_709_:
{
uint8_t v___x_719_; 
v___x_719_ = lean_strict_and(v___y_715_, v___y_718_);
if (v___y_711_ == 0)
{
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_713_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___x_719_;
v___y_691_ = v_a_436_;
v___y_692_ = v_a_437_;
goto v___jp_682_;
}
else
{
if (v_wantsRebuild_457_ == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_inc(v_spinnerIdx_461_);
lean_inc(v_lastUpdate_460_);
lean_inc_ref(v_resetCtrl_459_);
lean_inc_ref(v_failures_458_);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_727_ = lean_ctor_get(v_a_437_, 5);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_a_437_, 4);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_a_437_, 3);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_a_437_, 2);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_a_437_, 1);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_a_437_, 0);
lean_dec(v_unused_732_);
v___x_721_ = v_a_437_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_dec(v_a_437_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
lean_inc(v_totalJobs_456_);
lean_inc(v_jobNo_455_);
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_jobNo_455_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_totalJobs_456_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_failures_458_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_resetCtrl_459_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_lastUpdate_460_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v_spinnerIdx_461_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*6, v___y_711_);
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_713_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___x_719_;
v___y_691_ = v_a_436_;
v___y_692_ = v___x_724_;
goto v___jp_682_;
}
}
}
else
{
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_713_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___x_719_;
v___y_691_ = v_a_436_;
v___y_692_ = v_a_437_;
goto v___jp_682_;
}
}
}
v___jp_733_:
{
uint8_t v___x_742_; 
v___x_742_ = l_Lake_instOrdLogLevel_ord(v_failLv_464_, v___y_734_);
if (v___x_742_ == 2)
{
uint8_t v___x_743_; 
v___x_743_ = 0;
v___y_710_ = v___y_734_;
v___y_711_ = v___y_736_;
v___y_712_ = v___y_735_;
v___y_713_ = v___y_738_;
v___y_714_ = v___y_737_;
v___y_715_ = v___y_741_;
v___y_716_ = v___y_739_;
v___y_717_ = v___y_740_;
v___y_718_ = v___x_743_;
goto v___jp_709_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = 1;
v___y_710_ = v___y_734_;
v___y_711_ = v___y_736_;
v___y_712_ = v___y_735_;
v___y_713_ = v___y_738_;
v___y_714_ = v___y_737_;
v___y_715_ = v___y_741_;
v___y_716_ = v___y_739_;
v___y_717_ = v___y_740_;
v___y_718_ = v___x_744_;
goto v___jp_709_;
}
}
v___jp_745_:
{
lean_object* v_log_747_; uint8_t v_action_748_; uint8_t v_wantsRebuild_749_; lean_object* v_buildTime_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_log_747_ = lean_ctor_get(v___y_746_, 0);
lean_inc_ref(v_log_747_);
v_action_748_ = lean_ctor_get_uint8(v___y_746_, sizeof(void*)*3);
v_wantsRebuild_749_ = lean_ctor_get_uint8(v___y_746_, sizeof(void*)*3 + 1);
v_buildTime_750_ = lean_ctor_get(v___y_746_, 2);
lean_inc(v_buildTime_750_);
lean_dec_ref(v___y_746_);
v___x_751_ = l_Lake_Log_maxLv(v_log_747_);
v___x_752_ = lean_array_get_size(v_log_747_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_nat_dec_eq(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
uint8_t v___x_755_; 
v___x_755_ = 1;
v___y_734_ = v___x_751_;
v___y_735_ = v_log_747_;
v___y_736_ = v_wantsRebuild_749_;
v___y_737_ = v_buildTime_750_;
v___y_738_ = v___x_753_;
v___y_739_ = v___x_752_;
v___y_740_ = v_action_748_;
v___y_741_ = v___x_755_;
goto v___jp_733_;
}
else
{
uint8_t v___x_756_; 
v___x_756_ = 0;
v___y_734_ = v___x_751_;
v___y_735_ = v_log_747_;
v___y_736_ = v_wantsRebuild_749_;
v___y_737_ = v_buildTime_750_;
v___y_738_ = v___x_753_;
v___y_739_ = v___x_752_;
v___y_740_ = v_action_748_;
v___y_741_ = v___x_756_;
goto v___jp_733_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_759_, v_a_760_, v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_764_, uint8_t v___y_765_, uint8_t v_useAnsi_766_, lean_object* v_as_767_, size_t v_i_768_, size_t v_stop_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_764_, v___y_765_, v_useAnsi_766_, v_as_767_, v_i_768_, v_stop_769_, v_b_770_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_775_, lean_object* v___y_776_, lean_object* v_useAnsi_777_, lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v___y_14476__boxed_785_; uint8_t v_useAnsi_14477__boxed_786_; size_t v_i_boxed_787_; size_t v_stop_boxed_788_; lean_object* v_res_789_; 
v___y_14476__boxed_785_ = lean_unbox(v___y_776_);
v_useAnsi_14477__boxed_786_ = lean_unbox(v_useAnsi_777_);
v_i_boxed_787_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_788_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_775_, v___y_14476__boxed_785_, v_useAnsi_14477__boxed_786_, v_as_778_, v_i_boxed_787_, v_stop_boxed_788_, v_b_781_, v___y_782_, v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v_as_778_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_jobs_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_jobNo_799_; lean_object* v_totalJobs_800_; uint8_t v_wantsRebuild_801_; lean_object* v_failures_802_; lean_object* v_resetCtrl_803_; lean_object* v_lastUpdate_804_; lean_object* v_spinnerIdx_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v_jobs_795_ = lean_ctor_get(v_a_792_, 0);
v___x_796_ = lean_st_ref_take(v_jobs_795_);
v___x_797_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_798_ = lean_st_ref_put(v_jobs_795_, v___x_797_);
v_jobNo_799_ = lean_ctor_get(v_a_793_, 0);
v_totalJobs_800_ = lean_ctor_get(v_a_793_, 1);
v_wantsRebuild_801_ = lean_ctor_get_uint8(v_a_793_, sizeof(void*)*6);
v_failures_802_ = lean_ctor_get(v_a_793_, 2);
v_resetCtrl_803_ = lean_ctor_get(v_a_793_, 3);
v_lastUpdate_804_ = lean_ctor_get(v_a_793_, 4);
v_spinnerIdx_805_ = lean_ctor_get(v_a_793_, 5);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_793_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v_a_793_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_spinnerIdx_805_);
lean_inc(v_lastUpdate_804_);
lean_inc(v_resetCtrl_803_);
lean_inc(v_failures_802_);
lean_inc(v_totalJobs_800_);
lean_inc(v_jobNo_799_);
lean_dec(v_a_793_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_809_ = lean_array_get_size(v___x_796_);
v___x_810_ = lean_nat_add(v_totalJobs_800_, v___x_809_);
lean_dec(v_totalJobs_800_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_jobNo_799_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_failures_802_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_resetCtrl_803_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_lastUpdate_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 5, v_spinnerIdx_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_814_, sizeof(void*)*6, v_wantsRebuild_801_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_796_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_816_, v_a_817_);
lean_dec_ref(v_a_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object* v_as_820_, size_t v_i_821_, size_t v_stop_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_fst_828_; lean_object* v_snd_829_; uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_eq(v_i_821_, v_stop_822_);
if (v___x_833_ == 0)
{
lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v___x_836_; lean_object* v_task_837_; uint8_t v___x_838_; 
v_fst_834_ = lean_ctor_get(v_b_823_, 0);
v_snd_835_ = lean_ctor_get(v_b_823_, 1);
v___x_836_ = lean_array_uget_borrowed(v_as_820_, v_i_821_);
v_task_837_ = lean_ctor_get(v___x_836_, 0);
v___x_838_ = lean_io_get_task_state(v_task_837_);
switch(v___x_838_)
{
case 0:
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
lean_inc(v_snd_835_);
lean_inc(v_fst_834_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_b_823_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; 
v_unused_847_ = lean_ctor_get(v_b_823_, 1);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_b_823_, 0);
lean_dec(v_unused_848_);
v___x_840_ = v_b_823_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_b_823_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_inc(v___x_836_);
v___x_842_ = lean_array_push(v_snd_835_, v___x_836_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v_fst_828_ = v___x_844_;
v_snd_829_ = v___y_825_;
goto v___jp_827_;
}
}
}
case 1:
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_857_; 
lean_inc(v_snd_835_);
lean_inc(v_fst_834_);
v_isSharedCheck_857_ = !lean_is_exclusive(v_b_823_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_858_ = lean_ctor_get(v_b_823_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_b_823_, 0);
lean_dec(v_unused_859_);
v___x_850_ = v_b_823_;
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
else
{
lean_dec(v_b_823_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
lean_inc_n(v___x_836_, 2);
v___x_852_ = lean_array_push(v_fst_834_, v___x_836_);
v___x_853_ = lean_array_push(v_snd_835_, v___x_836_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_853_);
lean_ctor_set(v___x_850_, 0, v___x_852_);
v___x_855_ = v___x_850_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
v_fst_828_ = v___x_855_;
v_snd_829_ = v___y_825_;
goto v___jp_827_;
}
}
}
default: 
{
lean_object* v___x_860_; lean_object* v_snd_861_; lean_object* v_jobNo_862_; lean_object* v_totalJobs_863_; uint8_t v_wantsRebuild_864_; lean_object* v_failures_865_; lean_object* v_resetCtrl_866_; lean_object* v_lastUpdate_867_; lean_object* v_spinnerIdx_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_877_; 
lean_inc(v___x_836_);
v___x_860_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_836_, v___y_824_, v___y_825_);
v_snd_861_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_snd_861_);
lean_dec_ref(v___x_860_);
v_jobNo_862_ = lean_ctor_get(v_snd_861_, 0);
v_totalJobs_863_ = lean_ctor_get(v_snd_861_, 1);
v_wantsRebuild_864_ = lean_ctor_get_uint8(v_snd_861_, sizeof(void*)*6);
v_failures_865_ = lean_ctor_get(v_snd_861_, 2);
v_resetCtrl_866_ = lean_ctor_get(v_snd_861_, 3);
v_lastUpdate_867_ = lean_ctor_get(v_snd_861_, 4);
v_spinnerIdx_868_ = lean_ctor_get(v_snd_861_, 5);
v_isSharedCheck_877_ = !lean_is_exclusive(v_snd_861_);
if (v_isSharedCheck_877_ == 0)
{
v___x_870_ = v_snd_861_;
v_isShared_871_ = v_isSharedCheck_877_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_spinnerIdx_868_);
lean_inc(v_lastUpdate_867_);
lean_inc(v_resetCtrl_866_);
lean_inc(v_failures_865_);
lean_inc(v_totalJobs_863_);
lean_inc(v_jobNo_862_);
lean_dec(v_snd_861_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_877_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_add(v_jobNo_862_, v___x_872_);
lean_dec(v_jobNo_862_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_873_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_totalJobs_863_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_failures_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_resetCtrl_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_lastUpdate_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 5, v_spinnerIdx_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*6, v_wantsRebuild_864_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_fst_828_ = v_b_823_;
v_snd_829_ = v___x_875_;
goto v___jp_827_;
}
}
}
}
}
else
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_b_823_);
lean_ctor_set(v___x_878_, 1, v___y_825_);
return v___x_878_;
}
v___jp_827_:
{
size_t v___x_830_; size_t v___x_831_; 
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_821_, v___x_830_);
v_i_821_ = v___x_831_;
v_b_823_ = v_fst_828_;
v___y_825_ = v_snd_829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object* v_as_879_, lean_object* v_i_880_, lean_object* v_stop_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
size_t v_i_boxed_886_; size_t v_stop_boxed_887_; lean_object* v_res_888_; 
v_i_boxed_886_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_stop_boxed_887_ = lean_unbox_usize(v_stop_881_);
lean_dec(v_stop_881_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_879_, v_i_boxed_886_, v_stop_boxed_887_, v_b_882_, v___y_883_, v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec_ref(v_as_879_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object* v_new_891_, lean_object* v_unfinished_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___y_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___y_911_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_914_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_915_ = lean_array_get_size(v_unfinished_892_);
v___x_916_ = lean_nat_dec_lt(v___x_896_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_inc_ref(v_a_894_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_914_);
lean_ctor_set(v___x_917_, 1, v_a_894_);
v___y_898_ = v___x_917_;
v_fst_899_ = v___x_914_;
v_snd_900_ = v_a_894_;
goto v___jp_897_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = lean_nat_dec_le(v___x_915_, v___x_915_);
if (v___x_918_ == 0)
{
if (v___x_916_ == 0)
{
lean_object* v___x_919_; 
lean_inc_ref(v_a_894_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_914_);
lean_ctor_set(v___x_919_, 1, v_a_894_);
v___y_898_ = v___x_919_;
v_fst_899_ = v___x_914_;
v_snd_900_ = v_a_894_;
goto v___jp_897_;
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((size_t)0ULL);
v___x_921_ = lean_usize_of_nat(v___x_915_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_892_, v___x_920_, v___x_921_, v___x_914_, v_a_893_, v_a_894_);
v___y_911_ = v___x_922_;
goto v___jp_910_;
}
}
else
{
size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_915_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_892_, v___x_923_, v___x_924_, v___x_914_, v_a_893_, v_a_894_);
v___y_911_ = v___x_925_;
goto v___jp_910_;
}
}
v___jp_897_:
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_array_get_size(v_new_891_);
v___x_902_ = lean_nat_dec_lt(v___x_896_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_snd_900_);
lean_dec_ref(v_fst_899_);
return v___y_898_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = lean_nat_dec_le(v___x_901_, v___x_901_);
if (v___x_903_ == 0)
{
if (v___x_902_ == 0)
{
lean_dec_ref(v_snd_900_);
lean_dec_ref(v_fst_899_);
return v___y_898_;
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v___y_898_);
v___x_904_ = ((size_t)0ULL);
v___x_905_ = lean_usize_of_nat(v___x_901_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_891_, v___x_904_, v___x_905_, v_fst_899_, v_a_893_, v_snd_900_);
return v___x_906_;
}
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
lean_dec_ref(v___y_898_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = lean_usize_of_nat(v___x_901_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_891_, v___x_907_, v___x_908_, v_fst_899_, v_a_893_, v_snd_900_);
return v___x_909_;
}
}
}
v___jp_910_:
{
lean_object* v_fst_912_; lean_object* v_snd_913_; 
v_fst_912_ = lean_ctor_get(v___y_911_, 0);
lean_inc(v_fst_912_);
v_snd_913_ = lean_ctor_get(v___y_911_, 1);
lean_inc(v_snd_913_);
v___y_898_ = v___y_911_;
v_fst_899_ = v_fst_912_;
v_snd_900_ = v_snd_913_;
goto v___jp_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_926_, lean_object* v_unfinished_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_926_, v_unfinished_927_, v_a_928_, v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_unfinished_927_);
lean_dec_ref(v_new_926_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___y_936_; lean_object* v___x_954_; lean_object* v_lastUpdate_955_; lean_object* v_updateFrequency_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_954_ = lean_io_mono_ms_now();
v_lastUpdate_955_ = lean_ctor_get(v_a_933_, 4);
v_updateFrequency_956_ = lean_ctor_get(v_a_932_, 2);
v___x_957_ = lean_nat_sub(v___x_954_, v_lastUpdate_955_);
lean_dec(v___x_954_);
v___x_958_ = lean_nat_sub(v_updateFrequency_956_, v___x_957_);
lean_dec(v___x_957_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_nat_dec_lt(v___x_959_, v___x_958_);
if (v___x_960_ == 0)
{
lean_dec(v___x_958_);
v___y_936_ = v_a_933_;
goto v___jp_935_;
}
else
{
uint32_t v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_uint32_of_nat(v___x_958_);
lean_dec(v___x_958_);
v___x_962_ = l_IO_sleep(v___x_961_);
v___y_936_ = v_a_933_;
goto v___jp_935_;
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v_jobNo_938_; lean_object* v_totalJobs_939_; uint8_t v_wantsRebuild_940_; lean_object* v_failures_941_; lean_object* v_resetCtrl_942_; lean_object* v_spinnerIdx_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_952_; 
v___x_937_ = lean_io_mono_ms_now();
v_jobNo_938_ = lean_ctor_get(v___y_936_, 0);
v_totalJobs_939_ = lean_ctor_get(v___y_936_, 1);
v_wantsRebuild_940_ = lean_ctor_get_uint8(v___y_936_, sizeof(void*)*6);
v_failures_941_ = lean_ctor_get(v___y_936_, 2);
v_resetCtrl_942_ = lean_ctor_get(v___y_936_, 3);
v_spinnerIdx_943_ = lean_ctor_get(v___y_936_, 5);
v_isSharedCheck_952_ = !lean_is_exclusive(v___y_936_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___y_936_, 4);
lean_dec(v_unused_953_);
v___x_945_ = v___y_936_;
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_spinnerIdx_943_);
lean_inc(v_resetCtrl_942_);
lean_inc(v_failures_941_);
lean_inc(v_totalJobs_939_);
lean_inc(v_jobNo_938_);
lean_dec(v___y_936_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_box(0);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 4, v___x_937_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_jobNo_938_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_totalJobs_939_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_failures_941_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_resetCtrl_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_951_, 5, v_spinnerIdx_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*6, v_wantsRebuild_940_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_947_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_963_, v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_967_, lean_object* v_unfinished_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___y_978_; lean_object* v___y_979_; uint8_t v_failFast_1005_; 
v___x_972_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_967_, v_unfinished_968_, v_a_969_, v_a_970_);
lean_dec_ref(v_unfinished_968_);
lean_dec_ref(v_new_967_);
v_fst_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_fst_973_);
v_snd_974_ = lean_ctor_get(v___x_972_, 1);
lean_inc(v_snd_974_);
lean_dec_ref(v___x_972_);
v_fst_975_ = lean_ctor_get(v_fst_973_, 0);
lean_inc(v_fst_975_);
v_snd_976_ = lean_ctor_get(v_fst_973_, 1);
lean_inc(v_snd_976_);
lean_dec(v_fst_973_);
v_failFast_1005_ = lean_ctor_get_uint8(v_a_969_, sizeof(void*)*4 + 7);
if (v_failFast_1005_ == 0)
{
v___y_978_ = v_a_969_;
v___y_979_ = v_snd_974_;
goto v___jp_977_;
}
else
{
lean_object* v_cancelTk_x3f_1006_; 
v_cancelTk_x3f_1006_ = lean_ctor_get(v_a_969_, 3);
if (lean_obj_tag(v_cancelTk_x3f_1006_) == 1)
{
lean_object* v_val_1007_; lean_object* v_failures_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_val_1007_ = lean_ctor_get(v_cancelTk_x3f_1006_, 0);
v_failures_1008_ = lean_ctor_get(v_snd_974_, 2);
v___x_1009_ = lean_array_get_size(v_failures_1008_);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_nat_dec_eq(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = l_IO_CancelToken_set(v_val_1007_);
v___y_978_ = v_a_969_;
v___y_979_ = v_snd_974_;
goto v___jp_977_;
}
else
{
v___y_978_ = v_a_969_;
v___y_979_ = v_snd_974_;
goto v___jp_977_;
}
}
else
{
v___y_978_ = v_a_969_;
v___y_979_ = v_snd_974_;
goto v___jp_977_;
}
}
v___jp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_array_get_size(v_snd_976_);
v___x_982_ = lean_nat_dec_lt(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_fst_975_);
v___x_983_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_978_, v___y_979_);
v_fst_984_ = lean_ctor_get(v___x_983_, 0);
v_snd_985_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_996_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_985_);
lean_inc(v_fst_984_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_array_get_size(v_fst_984_);
v___x_990_ = lean_nat_dec_lt(v___x_980_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v_fst_984_);
lean_dec(v_snd_976_);
v___x_991_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_991_);
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_snd_985_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_del_object(v___x_987_);
v_new_967_ = v_fst_984_;
v_unfinished_968_ = v_snd_976_;
v_a_969_ = v___y_978_;
v_a_970_ = v_snd_985_;
goto _start;
}
}
}
else
{
lean_object* v___x_997_; lean_object* v_snd_998_; lean_object* v___x_999_; lean_object* v_snd_1000_; lean_object* v___x_1001_; lean_object* v_fst_1002_; lean_object* v_snd_1003_; 
v___x_997_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_975_, v_snd_976_, v___y_978_, v___y_979_);
lean_dec(v_fst_975_);
v_snd_998_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_snd_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v___y_978_, v_snd_998_);
v_snd_1000_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_978_, v_snd_1000_);
v_fst_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_fst_1002_);
v_snd_1003_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_snd_1003_);
lean_dec_ref(v___x_1001_);
v_new_967_ = v_fst_1002_;
v_unfinished_968_ = v_snd_976_;
v_a_969_ = v___y_978_;
v_a_970_ = v_snd_1003_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1013_, lean_object* v_unfinished_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1013_, v_unfinished_1014_, v_a_1015_, v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1094_; 
v___x_1023_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1020_, v_a_1021_);
v_fst_1024_ = lean_ctor_get(v___x_1023_, 0);
v_snd_1025_ = lean_ctor_get(v___x_1023_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1027_ = v___x_1023_;
v_isShared_1028_ = v_isSharedCheck_1094_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snd_1025_);
lean_inc(v_fst_1024_);
lean_dec(v___x_1023_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1094_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v_snd_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1092_; 
v___x_1029_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1024_, v_init_1019_, v_a_1020_, v_snd_1025_);
v_snd_1030_ = lean_ctor_get(v___x_1029_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1029_, 0);
lean_dec(v_unused_1093_);
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1092_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1092_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_jobNo_1034_; lean_object* v_totalJobs_1035_; uint8_t v_wantsRebuild_1036_; lean_object* v_failures_1037_; lean_object* v_resetCtrl_1038_; lean_object* v_lastUpdate_1039_; lean_object* v_spinnerIdx_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1091_; 
v_jobNo_1034_ = lean_ctor_get(v_snd_1030_, 0);
v_totalJobs_1035_ = lean_ctor_get(v_snd_1030_, 1);
v_wantsRebuild_1036_ = lean_ctor_get_uint8(v_snd_1030_, sizeof(void*)*6);
v_failures_1037_ = lean_ctor_get(v_snd_1030_, 2);
v_resetCtrl_1038_ = lean_ctor_get(v_snd_1030_, 3);
v_lastUpdate_1039_ = lean_ctor_get(v_snd_1030_, 4);
v_spinnerIdx_1040_ = lean_ctor_get(v_snd_1030_, 5);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_snd_1030_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1042_ = v_snd_1030_;
v_isShared_1043_ = v_isSharedCheck_1091_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_spinnerIdx_1040_);
lean_inc(v_lastUpdate_1039_);
lean_inc(v_resetCtrl_1038_);
lean_inc(v_failures_1037_);
lean_inc(v_totalJobs_1035_);
lean_inc(v_jobNo_1034_);
lean_dec(v_snd_1030_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1091_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 3, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_jobNo_1034_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_totalJobs_1035_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_failures_1037_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_lastUpdate_1039_);
lean_ctor_set(v_reuseFailAlloc_1090_, 5, v_spinnerIdx_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*6, v_wantsRebuild_1036_);
v___x_1046_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v_val_1048_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = lean_string_utf8_byte_size(v_resetCtrl_1038_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_nat_dec_eq(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v_out_1055_; lean_object* v_flush_1056_; lean_object* v_putStr_1057_; lean_object* v___x_1062_; 
lean_del_object(v___x_1027_);
v_out_1055_ = lean_ctor_get(v_a_1020_, 1);
v_flush_1056_ = lean_ctor_get(v_out_1055_, 0);
v_putStr_1057_ = lean_ctor_get(v_out_1055_, 4);
lean_inc_ref(v_putStr_1057_);
lean_inc_ref(v_resetCtrl_1038_);
v___x_1062_ = lean_apply_2(v_putStr_1057_, v_resetCtrl_1038_, lean_box(0));
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_dec_ref_known(v___x_1062_, 1);
lean_dec_ref(v_resetCtrl_1038_);
goto v___jp_1058_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1085_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1085_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1085_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1067_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1068_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1069_ = lean_unsigned_to_nat(82u);
v___x_1070_ = lean_unsigned_to_nat(4u);
v___x_1071_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1072_ = lean_io_error_to_string(v_a_1063_);
v___x_1073_ = lean_string_append(v___x_1071_, v___x_1072_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1075_ = lean_string_append(v___x_1073_, v___x_1074_);
v___x_1076_ = l_String_quote(v_resetCtrl_1038_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 3);
lean_ctor_set(v___x_1065_, 0, v___x_1076_);
v___x_1078_ = v___x_1065_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1079_ = l_Std_Format_defWidth;
v___x_1080_ = l_Std_Format_pretty(v___x_1078_, v___x_1079_, v___x_1053_, v___x_1053_);
v___x_1081_ = lean_string_append(v___x_1075_, v___x_1080_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = l_mkPanicMessageWithDecl(v___x_1067_, v___x_1068_, v___x_1069_, v___x_1070_, v___x_1081_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1082_);
goto v___jp_1058_;
}
}
}
v___jp_1058_:
{
lean_object* v___x_1059_; 
lean_inc_ref(v_flush_1056_);
v___x_1059_ = lean_apply_1(v_flush_1056_, lean_box(0));
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v_val_1048_ = v_a_1060_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1061_; 
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_box(0);
v_val_1048_ = v___x_1061_;
goto v___jp_1047_;
}
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec_ref(v_resetCtrl_1038_);
lean_del_object(v___x_1032_);
v___x_1086_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 1, v___x_1046_);
lean_ctor_set(v___x_1027_, 0, v___x_1086_);
v___x_1088_ = v___x_1027_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1046_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
v___jp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1046_);
lean_ctor_set(v___x_1032_, 0, v_val_1048_);
v___x_1050_ = v___x_1032_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_val_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1046_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1095_, v_a_1096_, v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1100_){
_start:
{
lean_object* v_failures_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_failures_1101_ = lean_ctor_get(v_self_1100_, 0);
v___x_1102_ = lean_array_get_size(v_failures_1101_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_nat_dec_eq(v___x_1102_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1105_){
_start:
{
uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1105_);
lean_dec_ref(v_self_1105_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0(void){
_start:
{
uint8_t v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = 2;
v___x_1109_ = l_Lake_Verbosity_ctorIdx(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1110_, lean_object* v_jobs_1111_, lean_object* v_cancelTk_x3f_1112_){
_start:
{
lean_object* v_toLogConfig_1114_; uint8_t v_failFast_1115_; uint8_t v_verbosity_1116_; uint8_t v_failLv_1117_; uint8_t v_outLv_1118_; uint8_t v_ansiMode_1119_; lean_object* v_out_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; uint8_t v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1133_; 
v_toLogConfig_1114_ = lean_ctor_get(v_cfg_1110_, 0);
v_failFast_1115_ = lean_ctor_get_uint8(v_cfg_1110_, sizeof(void*)*5 + 3);
v_verbosity_1116_ = lean_ctor_get_uint8(v_cfg_1110_, sizeof(void*)*5 + 4);
v_failLv_1117_ = lean_ctor_get_uint8(v_toLogConfig_1114_, sizeof(void*)*1);
v_outLv_1118_ = lean_ctor_get_uint8(v_toLogConfig_1114_, sizeof(void*)*1 + 1);
v_ansiMode_1119_ = lean_ctor_get_uint8(v_toLogConfig_1114_, sizeof(void*)*1 + 2);
v_out_1120_ = lean_ctor_get(v_toLogConfig_1114_, 0);
v___x_1121_ = l_Lake_OutStream_get(v_out_1120_);
lean_inc_ref(v___x_1121_);
v___x_1122_ = l_Lake_AnsiMode_isEnabled(v___x_1121_, v_ansiMode_1119_);
v___x_1123_ = l_Lake_BuildConfig_showProgress(v_cfg_1110_);
v___x_1124_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1116_);
v___x_1125_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0, &l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0);
v___x_1126_ = lean_nat_dec_eq(v___x_1124_, v___x_1125_);
lean_dec(v___x_1124_);
if (v___x_1126_ == 0)
{
uint8_t v___x_1135_; 
v___x_1135_ = 3;
v___y_1133_ = v___x_1135_;
goto v___jp_1132_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = 0;
v___y_1133_ = v___x_1136_;
goto v___jp_1132_;
}
v___jp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(100u);
v___x_1131_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_1131_, 0, v_jobs_1111_);
lean_ctor_set(v___x_1131_, 1, v___x_1121_);
lean_ctor_set(v___x_1131_, 2, v___x_1130_);
lean_ctor_set(v___x_1131_, 3, v_cancelTk_x3f_1112_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4, v_outLv_1118_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 1, v_failLv_1117_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 2, v___y_1128_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 3, v___x_1126_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 4, v___x_1122_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 5, v___x_1123_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 6, v___y_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 7, v_failFast_1115_);
return v___x_1131_;
}
v___jp_1132_:
{
if (v___x_1126_ == 0)
{
if (v___x_1122_ == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = 1;
v___y_1128_ = v___y_1133_;
v___y_1129_ = v___x_1134_;
goto v___jp_1127_;
}
else
{
v___y_1128_ = v___y_1133_;
v___y_1129_ = v___x_1126_;
goto v___jp_1127_;
}
}
else
{
v___y_1128_ = v___y_1133_;
v___y_1129_ = v___x_1126_;
goto v___jp_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1137_, lean_object* v_jobs_1138_, lean_object* v_cancelTk_x3f_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1137_, v_jobs_1138_, v_cancelTk_x3f_1139_);
lean_dec_ref(v_cfg_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1142_, lean_object* v_initJobs_1143_, lean_object* v_initFailures_1144_, lean_object* v_resetCtrl_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v_snd_1152_; lean_object* v_totalJobs_1153_; uint8_t v_wantsRebuild_1154_; lean_object* v_failures_1155_; lean_object* v___x_1156_; 
v___x_1147_ = lean_io_mono_ms_now();
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = 0;
v___x_1150_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1148_);
lean_ctor_set(v___x_1150_, 2, v_initFailures_1144_);
lean_ctor_set(v___x_1150_, 3, v_resetCtrl_1145_);
lean_ctor_set(v___x_1150_, 4, v___x_1147_);
lean_ctor_set(v___x_1150_, 5, v___x_1148_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*6, v___x_1149_);
v___x_1151_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1143_, v_ctx_1142_, v___x_1150_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
lean_dec_ref(v___x_1151_);
v_totalJobs_1153_ = lean_ctor_get(v_snd_1152_, 1);
lean_inc(v_totalJobs_1153_);
v_wantsRebuild_1154_ = lean_ctor_get_uint8(v_snd_1152_, sizeof(void*)*6);
v_failures_1155_ = lean_ctor_get(v_snd_1152_, 2);
lean_inc_ref(v_failures_1155_);
lean_dec(v_snd_1152_);
v___x_1156_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1156_, 0, v_failures_1155_);
lean_ctor_set(v___x_1156_, 1, v_totalJobs_1153_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*2, v_wantsRebuild_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1157_, lean_object* v_initJobs_1158_, lean_object* v_initFailures_1159_, lean_object* v_resetCtrl_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1157_, v_initJobs_1158_, v_initFailures_1159_, v_resetCtrl_1160_);
lean_dec_ref(v_ctx_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1163_, lean_object* v_jobs_1164_, lean_object* v_out_1165_, uint8_t v_failLv_1166_, uint8_t v_outLv_1167_, uint8_t v_minAction_1168_, uint8_t v_showOptional_1169_, uint8_t v_useAnsi_1170_, uint8_t v_showProgress_1171_, uint8_t v_showTime_1172_, lean_object* v_resetCtrl_1173_, lean_object* v_initFailures_1174_, lean_object* v_updateFrequency_1175_){
_start:
{
uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v_ctx_1179_; lean_object* v___x_1180_; 
v___x_1177_ = 0;
v___x_1178_ = lean_box(0);
v_ctx_1179_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_ctx_1179_, 0, v_jobs_1164_);
lean_ctor_set(v_ctx_1179_, 1, v_out_1165_);
lean_ctor_set(v_ctx_1179_, 2, v_updateFrequency_1175_);
lean_ctor_set(v_ctx_1179_, 3, v___x_1178_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4, v_outLv_1167_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 1, v_failLv_1166_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 2, v_minAction_1168_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 3, v_showOptional_1169_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 4, v_useAnsi_1170_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 5, v_showProgress_1171_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 6, v_showTime_1172_);
lean_ctor_set_uint8(v_ctx_1179_, sizeof(void*)*4 + 7, v___x_1177_);
v___x_1180_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1179_, v_initJobs_1163_, v_initFailures_1174_, v_resetCtrl_1173_);
lean_dec_ref_known(v_ctx_1179_, 4);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1181_, lean_object* v_jobs_1182_, lean_object* v_out_1183_, lean_object* v_failLv_1184_, lean_object* v_outLv_1185_, lean_object* v_minAction_1186_, lean_object* v_showOptional_1187_, lean_object* v_useAnsi_1188_, lean_object* v_showProgress_1189_, lean_object* v_showTime_1190_, lean_object* v_resetCtrl_1191_, lean_object* v_initFailures_1192_, lean_object* v_updateFrequency_1193_, lean_object* v_a_1194_){
_start:
{
uint8_t v_failLv_boxed_1195_; uint8_t v_outLv_boxed_1196_; uint8_t v_minAction_boxed_1197_; uint8_t v_showOptional_boxed_1198_; uint8_t v_useAnsi_boxed_1199_; uint8_t v_showProgress_boxed_1200_; uint8_t v_showTime_boxed_1201_; lean_object* v_res_1202_; 
v_failLv_boxed_1195_ = lean_unbox(v_failLv_1184_);
v_outLv_boxed_1196_ = lean_unbox(v_outLv_1185_);
v_minAction_boxed_1197_ = lean_unbox(v_minAction_1186_);
v_showOptional_boxed_1198_ = lean_unbox(v_showOptional_1187_);
v_useAnsi_boxed_1199_ = lean_unbox(v_useAnsi_1188_);
v_showProgress_boxed_1200_ = lean_unbox(v_showProgress_1189_);
v_showTime_boxed_1201_ = lean_unbox(v_showTime_1190_);
v_res_1202_ = l_Lake_monitorJobs(v_initJobs_1181_, v_jobs_1182_, v_out_1183_, v_failLv_boxed_1195_, v_outLv_boxed_1196_, v_minAction_boxed_1197_, v_showOptional_boxed_1198_, v_useAnsi_boxed_1199_, v_showProgress_boxed_1200_, v_showTime_boxed_1201_, v_resetCtrl_1191_, v_initFailures_1192_, v_updateFrequency_1193_);
return v_res_1202_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1203_; 
v___x_1203_ = 3;
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(lean_object* v_logger_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_apply_2(v_logger_1204_, v___y_1206_, lean_box(0));
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed(lean_object* v_logger_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0(v_logger_1209_, v_x_1210_, v___y_1211_);
return v_res_1213_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1216_ = l_String_quote(v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__1);
v___x_1218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = l_Std_Format_defWidth;
v___x_1221_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__2);
v___x_1222_ = l_Std_Format_pretty(v___x_1221_, v___x_1220_, v___x_1219_, v___x_1219_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1230_ = l_String_quote(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__8);
v___x_1232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = l_Std_Format_defWidth;
v___x_1235_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__9);
v___x_1236_ = l_Std_Format_pretty(v___x_1235_, v___x_1234_, v___x_1233_, v___x_1233_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1239_ = l_String_quote(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__12);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Std_Format_defWidth;
v___x_1244_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__13);
v___x_1245_ = l_Std_Format_pretty(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1242_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1249_ = l_String_quote(v___x_1248_);
return v___x_1249_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__17);
v___x_1251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = l_Std_Format_defWidth;
v___x_1254_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__18);
v___x_1255_ = l_Std_Format_pretty(v___x_1254_, v___x_1253_, v___x_1252_, v___x_1252_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(lean_object* v_logger_1256_, lean_object* v_bctx_1257_, lean_object* v_out_1258_, lean_object* v_outputsFile_1259_){
_start:
{
lean_object* v___x_1267_; lean_object* v_outputsRef_x3f_1268_; 
v___x_1267_ = l_instMonadBaseIO;
v_outputsRef_x3f_1268_ = lean_ctor_get(v_bctx_1257_, 5);
lean_inc(v_outputsRef_x3f_1268_);
if (lean_obj_tag(v_outputsRef_x3f_1268_) == 1)
{
lean_object* v_toContext_1269_; lean_object* v_toBuildConfig_1270_; lean_object* v_val_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1418_; 
v_toContext_1269_ = lean_ctor_get(v_bctx_1257_, 1);
lean_inc(v_toContext_1269_);
v_toBuildConfig_1270_ = lean_ctor_get(v_bctx_1257_, 0);
lean_inc_ref(v_toBuildConfig_1270_);
lean_dec_ref(v_bctx_1257_);
v_val_1271_ = lean_ctor_get(v_outputsRef_x3f_1268_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_outputsRef_x3f_1268_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1273_ = v_outputsRef_x3f_1268_;
v_isShared_1274_ = v_isSharedCheck_1418_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_val_1271_);
lean_dec(v_outputsRef_x3f_1268_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1418_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_lakeEnv_1275_; lean_object* v_packages_1276_; uint8_t v_verbosity_1277_; lean_object* v_outputsIdx_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_lakeEnv_1275_ = lean_ctor_get(v_toContext_1269_, 0);
lean_inc_ref(v_lakeEnv_1275_);
v_packages_1276_ = lean_ctor_get(v_toContext_1269_, 4);
lean_inc_ref(v_packages_1276_);
lean_dec(v_toContext_1269_);
v_verbosity_1277_ = lean_ctor_get_uint8(v_toBuildConfig_1270_, sizeof(void*)*5 + 4);
v_outputsIdx_1278_ = lean_ctor_get(v_toBuildConfig_1270_, 2);
lean_inc(v_outputsIdx_1278_);
lean_dec_ref(v_toBuildConfig_1270_);
v___x_1279_ = lean_array_get_size(v_packages_1276_);
v___x_1280_ = lean_nat_dec_lt(v_outputsIdx_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v_putStr_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec(v_outputsIdx_1278_);
lean_dec_ref(v_packages_1276_);
lean_dec_ref(v_lakeEnv_1275_);
lean_del_object(v___x_1273_);
lean_dec(v_val_1271_);
lean_dec_ref(v_outputsFile_1259_);
lean_dec_ref(v_logger_1256_);
v_putStr_1281_ = lean_ctor_get(v_out_1258_, 4);
lean_inc_ref(v_putStr_1281_);
lean_dec_ref(v_out_1258_);
v___x_1282_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_1283_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1284_ = lean_apply_2(v_putStr_1281_, v___x_1282_, lean_box(0));
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref_known(v___x_1284_, 1);
goto v___jp_1263_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_2578__overap_1298_; lean_object* v___x_1299_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1287_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1288_ = lean_unsigned_to_nat(82u);
v___x_1289_ = lean_unsigned_to_nat(4u);
v___x_1290_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1291_ = lean_io_error_to_string(v_a_1285_);
v___x_1292_ = lean_string_append(v___x_1290_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1294_ = lean_string_append(v___x_1292_, v___x_1293_);
v___x_1295_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_1296_ = lean_string_append(v___x_1294_, v___x_1295_);
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1286_, v___x_1287_, v___x_1288_, v___x_1289_, v___x_1296_);
lean_dec_ref(v___x_1296_);
v___x_2578__overap_1298_ = l_panic___redArg(v___x_1283_, v___x_1297_);
v___x_1299_ = lean_apply_1(v___x_2578__overap_1298_, lean_box(0));
lean_dec(v___x_1299_);
goto v___jp_1263_;
}
}
else
{
lean_object* v___x_1300_; lean_object* v_config_1301_; lean_object* v_enableArtifactCache_x3f_1302_; lean_object* v___f_1303_; lean_object* v___y_1305_; lean_object* v___y_1306_; uint8_t v___y_1307_; lean_object* v___y_1317_; lean_object* v___y_1318_; uint8_t v___y_1327_; uint8_t v___y_1396_; uint8_t v___y_1405_; 
v___x_1300_ = lean_array_fget(v_packages_1276_, v_outputsIdx_1278_);
lean_dec(v_outputsIdx_1278_);
v_config_1301_ = lean_ctor_get(v___x_1300_, 6);
v_enableArtifactCache_x3f_1302_ = lean_ctor_get(v_config_1301_, 24);
lean_inc_ref(v_logger_1256_);
v___f_1303_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1303_, 0, v_logger_1256_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1302_) == 0)
{
lean_object* v_enableArtifactCache_x3f_1406_; 
v_enableArtifactCache_x3f_1406_ = lean_ctor_get(v_lakeEnv_1275_, 6);
lean_inc(v_enableArtifactCache_x3f_1406_);
lean_dec_ref(v_lakeEnv_1275_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1406_) == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_config_1409_; lean_object* v_enableArtifactCache_x3f_1410_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_array_fget(v_packages_1276_, v___x_1407_);
lean_dec_ref(v_packages_1276_);
v_config_1409_ = lean_ctor_get(v___x_1408_, 6);
lean_inc_ref(v_config_1409_);
lean_dec(v___x_1408_);
v_enableArtifactCache_x3f_1410_ = lean_ctor_get(v_config_1409_, 24);
lean_inc(v_enableArtifactCache_x3f_1410_);
lean_dec_ref(v_config_1409_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1410_) == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = 0;
v___y_1396_ = v___x_1411_;
goto v___jp_1395_;
}
else
{
lean_object* v_val_1412_; uint8_t v___x_1413_; 
v_val_1412_ = lean_ctor_get(v_enableArtifactCache_x3f_1410_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1410_, 1);
v___x_1413_ = lean_unbox(v_val_1412_);
lean_dec(v_val_1412_);
v___y_1405_ = v___x_1413_;
goto v___jp_1404_;
}
}
else
{
lean_object* v_val_1414_; uint8_t v___x_1415_; 
lean_dec_ref(v_packages_1276_);
v_val_1414_ = lean_ctor_get(v_enableArtifactCache_x3f_1406_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v_enableArtifactCache_x3f_1406_, 1);
v___x_1415_ = lean_unbox(v_val_1414_);
lean_dec(v_val_1414_);
v___y_1405_ = v___x_1415_;
goto v___jp_1404_;
}
}
else
{
lean_object* v_val_1416_; uint8_t v___x_1417_; 
lean_dec_ref(v_packages_1276_);
lean_dec_ref(v_lakeEnv_1275_);
v_val_1416_ = lean_ctor_get(v_enableArtifactCache_x3f_1302_, 0);
v___x_1417_ = lean_unbox(v_val_1416_);
v___y_1405_ = v___x_1417_;
goto v___jp_1404_;
}
v___jp_1304_:
{
if (v___y_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___f_1303_);
v___x_1308_ = lean_box(0);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = lean_array_get_size(v___y_1306_);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_nat_dec_lt(v___y_1305_, v___x_1309_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___f_1303_);
return v___x_1310_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_2392__overap_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1309_);
v___x_2392__overap_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1267_, v___f_1303_, v___y_1306_, v___x_1312_, v___x_1313_, v___x_1310_);
v___x_1315_ = lean_apply_1(v___x_2392__overap_1314_, lean_box(0));
return v___x_1315_;
}
}
}
v___jp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_array_get_size(v___y_1318_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_nat_dec_lt(v___y_1317_, v___x_1319_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___f_1303_);
return v___x_1320_;
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_2322__overap_1324_; lean_object* v___x_1325_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1319_);
v___x_2322__overap_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1267_, v___f_1303_, v___y_1318_, v___x_1322_, v___x_1323_, v___x_1320_);
v___x_1325_ = lean_apply_1(v___x_2322__overap_1324_, lean_box(0));
return v___x_1325_;
}
}
v___jp_1326_:
{
lean_object* v___x_1328_; lean_object* v_config_1329_; lean_object* v_toLeanConfig_1330_; lean_object* v_platformIndependent_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1328_ = lean_st_ref_get(v_val_1271_);
lean_dec(v_val_1271_);
v_config_1329_ = lean_ctor_get(v___x_1300_, 6);
lean_inc_ref(v_config_1329_);
lean_dec(v___x_1300_);
v_toLeanConfig_1330_ = lean_ctor_get(v_config_1329_, 1);
lean_inc_ref(v_toLeanConfig_1330_);
lean_dec_ref(v_config_1329_);
v_platformIndependent_1331_ = lean_ctor_get(v_toLeanConfig_1330_, 10);
lean_inc(v_platformIndependent_1331_);
lean_dec_ref(v_toLeanConfig_1330_);
v___f_1332_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__5));
v___x_1333_ = lean_box(v___x_1280_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1333_);
v___x_1335_ = v___x_1273_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1336_ = l_Option_instBEq_beq___redArg(v___f_1332_, v_platformIndependent_1331_, v___x_1335_);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_1339_ = l_Lake_CacheMap_writeFile(v_outputsFile_1259_, v___x_1328_, v___x_1336_, v___x_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 2);
v___x_1341_ = lean_array_get_size(v_a_1340_);
v___x_1342_ = lean_nat_dec_eq(v___x_1341_, v___x_1337_);
if (v___x_1342_ == 0)
{
if (v___y_1327_ == 0)
{
lean_dec(v_a_1340_);
lean_dec_ref(v___f_1303_);
lean_dec_ref(v_out_1258_);
goto v___jp_1261_;
}
else
{
lean_object* v_putStr_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_putStr_1343_ = lean_ctor_get(v_out_1258_, 4);
lean_inc_ref(v_putStr_1343_);
lean_dec_ref(v_out_1258_);
v___x_1344_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_1345_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1346_ = lean_apply_2(v_putStr_1343_, v___x_1344_, lean_box(0));
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_dec_ref_known(v___x_1346_, 1);
v___y_1317_ = v___x_1337_;
v___y_1318_ = v_a_1340_;
goto v___jp_1316_;
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_2586__overap_1365_; lean_object* v___x_1366_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1349_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1350_ = lean_unsigned_to_nat(82u);
v___x_1351_ = lean_unsigned_to_nat(4u);
v___x_1352_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1353_, v___y_1327_);
v___x_1355_ = lean_string_append(v___x_1352_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_io_error_to_string(v_a_1347_);
v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
v___x_1364_ = l_mkPanicMessageWithDecl(v___x_1348_, v___x_1349_, v___x_1350_, v___x_1351_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_2586__overap_1365_ = l_panic___redArg(v___x_1345_, v___x_1364_);
v___x_1366_ = lean_apply_1(v___x_2586__overap_1365_, lean_box(0));
lean_dec(v___x_1366_);
v___y_1317_ = v___x_1337_;
v___y_1318_ = v_a_1340_;
goto v___jp_1316_;
}
}
}
else
{
lean_dec(v_a_1340_);
lean_dec_ref(v___f_1303_);
lean_dec_ref(v_out_1258_);
goto v___jp_1261_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v_putStr_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1367_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1339_, 2);
v_putStr_1368_ = lean_ctor_get(v_out_1258_, 4);
lean_inc_ref(v_putStr_1368_);
lean_dec_ref(v_out_1258_);
v___x_1369_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_1370_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1371_ = lean_apply_2(v_putStr_1368_, v___x_1369_, lean_box(0));
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_dec_ref_known(v___x_1371_, 1);
v___y_1305_ = v___x_1337_;
v___y_1306_ = v_a_1367_;
v___y_1307_ = v___y_1327_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_2591__overap_1390_; lean_object* v___x_1391_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1374_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1375_ = lean_unsigned_to_nat(82u);
v___x_1376_ = lean_unsigned_to_nat(4u);
v___x_1377_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1378_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1378_, v___x_1280_);
v___x_1380_ = lean_string_append(v___x_1377_, v___x_1379_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1382_ = lean_string_append(v___x_1380_, v___x_1381_);
v___x_1383_ = lean_io_error_to_string(v_a_1372_);
v___x_1384_ = lean_string_append(v___x_1382_, v___x_1383_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
v___x_1387_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
v___x_1389_ = l_mkPanicMessageWithDecl(v___x_1373_, v___x_1374_, v___x_1375_, v___x_1376_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_2591__overap_1390_ = l_panic___redArg(v___x_1370_, v___x_1389_);
v___x_1391_ = lean_apply_1(v___x_2591__overap_1390_, lean_box(0));
lean_dec(v___x_1391_);
v___y_1305_ = v___x_1337_;
v___y_1306_ = v_a_1367_;
v___y_1307_ = v___y_1327_;
goto v___jp_1304_;
}
}
}
}
v___jp_1393_:
{
if (v_verbosity_1277_ == 2)
{
v___y_1327_ = v___x_1280_;
goto v___jp_1326_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = 0;
v___y_1327_ = v___x_1394_;
goto v___jp_1326_;
}
}
v___jp_1395_:
{
lean_object* v_baseName_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_baseName_1397_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_baseName_1397_);
v___x_1398_ = l_Lean_Name_toString(v_baseName_1397_, v___y_1396_);
v___x_1399_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_1400_ = lean_string_append(v___x_1398_, v___x_1399_);
v___x_1401_ = 2;
v___x_1402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*1, v___x_1401_);
v___x_1403_ = lean_apply_2(v_logger_1256_, v___x_1402_, lean_box(0));
goto v___jp_1393_;
}
v___jp_1404_:
{
if (v___y_1405_ == 0)
{
v___y_1396_ = v___y_1405_;
goto v___jp_1395_;
}
else
{
lean_dec_ref(v_logger_1256_);
goto v___jp_1393_;
}
}
}
}
}
else
{
lean_object* v_putStr_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v_outputsRef_x3f_1268_);
lean_dec_ref(v_outputsFile_1259_);
lean_dec_ref(v_bctx_1257_);
lean_dec_ref(v_logger_1256_);
v_putStr_1419_ = lean_ctor_get(v_out_1258_, 4);
lean_inc_ref(v_putStr_1419_);
lean_dec_ref(v_out_1258_);
v___x_1420_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_1421_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1422_ = lean_apply_2(v_putStr_1419_, v___x_1420_, lean_box(0));
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_dec_ref_known(v___x_1422_, 1);
goto v___jp_1265_;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_2596__overap_1436_; lean_object* v___x_1437_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1426_ = lean_unsigned_to_nat(82u);
v___x_1427_ = lean_unsigned_to_nat(4u);
v___x_1428_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1429_ = lean_io_error_to_string(v_a_1423_);
v___x_1430_ = lean_string_append(v___x_1428_, v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1432_ = lean_string_append(v___x_1430_, v___x_1431_);
v___x_1433_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_1434_ = lean_string_append(v___x_1432_, v___x_1433_);
v___x_1435_ = l_mkPanicMessageWithDecl(v___x_1424_, v___x_1425_, v___x_1426_, v___x_1427_, v___x_1434_);
lean_dec_ref(v___x_1434_);
v___x_2596__overap_1436_ = l_panic___redArg(v___x_1421_, v___x_1435_);
v___x_1437_ = lean_apply_1(v___x_2596__overap_1436_, lean_box(0));
lean_dec(v___x_1437_);
goto v___jp_1265_;
}
}
v___jp_1261_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
v___jp_1263_:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_box(0);
return v___x_1264_;
}
v___jp_1265_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_box(0);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___boxed(lean_object* v_logger_1438_, lean_object* v_bctx_1439_, lean_object* v_out_1440_, lean_object* v_outputsFile_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs(v_logger_1438_, v_bctx_1439_, v_out_1440_, v_outputsFile_1441_);
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
lean_dec_ref_known(v___x_1463_, 1);
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
v___x_1471_ = lean_unsigned_to_nat(82u);
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
lean_dec_ref_known(v___x_1659_, 1);
goto v___jp_1648_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1662_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1663_ = lean_unsigned_to_nat(82u);
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
lean_dec_ref_known(v___x_1643_, 1);
return v_a_1644_;
}
else
{
lean_object* v___x_1645_; 
lean_dec_ref_known(v___x_1643_, 1);
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
v_showSuccess_1675_ = lean_ctor_get_uint8(v_cfg_1521_, sizeof(void*)*5 + 5);
v___y_1604_ = v_showSuccess_1675_;
goto v___jp_1603_;
}
}
v___jp_1525_:
{
uint8_t v_noBuild_1528_; 
v_noBuild_1528_ = lean_ctor_get_uint8(v_cfg_1521_, sizeof(void*)*5 + 2);
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
lean_dec_ref_known(v___x_1534_, 1);
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
v___x_1542_ = lean_unsigned_to_nat(82u);
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
lean_dec_ref_known(v___x_1570_, 1);
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
v___x_1578_ = lean_unsigned_to_nat(82u);
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
lean_dec_ref_known(v___x_1616_, 1);
return v_a_1617_;
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1618_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1619_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1620_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1621_ = lean_unsigned_to_nat(82u);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(lean_object* v_self_1681_){
_start:
{
lean_object* v_toMonitorResult_1682_; 
v_toMonitorResult_1682_ = lean_ctor_get(v_self_1681_, 0);
lean_inc_ref(v_toMonitorResult_1682_);
return v_toMonitorResult_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0___boxed(lean_object* v_self_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___lam__0(v_self_1683_);
lean_dec_ref(v_self_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg(){
_start:
{
lean_object* v___f_1687_; 
v___f_1687_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___boxed(lean_object* v___dummy_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg();
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1690_){
_start:
{
lean_object* v___f_1691_; 
v___f_1691_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___redArg___closed__0));
return v___f_1691_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1692_){
_start:
{
lean_object* v_out_1693_; 
v_out_1693_ = lean_ctor_get(v_self_1692_, 1);
if (lean_obj_tag(v_out_1693_) == 0)
{
uint8_t v___x_1694_; 
v___x_1694_ = 0;
return v___x_1694_;
}
else
{
uint8_t v___x_1695_; 
v___x_1695_ = 1;
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1696_){
_start:
{
uint8_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1696_);
lean_dec_ref(v_self_1696_);
v_r_1698_ = lean_box(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1699_, lean_object* v_self_1700_){
_start:
{
lean_object* v_out_1701_; 
v_out_1701_ = lean_ctor_get(v_self_1700_, 1);
if (lean_obj_tag(v_out_1701_) == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = 0;
return v___x_1702_;
}
else
{
uint8_t v___x_1703_; 
v___x_1703_ = 1;
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_self_1705_){
_start:
{
uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_res_1706_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1704_, v_self_1705_);
lean_dec_ref(v_self_1705_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1716_, lean_object* v_job_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_failures_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
lean_inc_ref(v_job_1717_);
v___x_1719_ = l_Lake_Job_toOpaque___redArg(v_job_1717_);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_mk_empty_array_with_capacity(v___x_1720_);
v___x_1722_ = lean_array_push(v___x_1721_, v___x_1719_);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1725_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1726_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1716_, v___x_1722_, v___x_1724_, v___x_1725_);
v_failures_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_ref(v_failures_1727_);
v___x_1728_ = lean_array_get_size(v_failures_1727_);
lean_dec_ref(v_failures_1727_);
v___x_1729_ = lean_nat_dec_eq(v___x_1728_, v___x_1723_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v_job_1717_);
v___x_1730_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1726_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v_task_1732_; lean_object* v___x_1733_; 
v_task_1732_ = lean_ctor_get(v_job_1717_, 0);
lean_inc_ref(v_task_1732_);
lean_dec_ref(v_job_1717_);
v___x_1733_ = lean_io_wait(v_task_1732_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1733_, 1);
lean_dec(v_unused_1743_);
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1738_);
lean_ctor_set(v___x_1736_, 0, v___x_1726_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1752_ = lean_ctor_get(v___x_1733_, 1);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1753_);
v___x_1745_ = v___x_1733_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_dec(v___x_1733_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1746_ == 0)
{
lean_ctor_set_tag(v___x_1745_, 0);
lean_ctor_set(v___x_1745_, 1, v___x_1747_);
lean_ctor_set(v___x_1745_, 0, v___x_1726_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1754_, lean_object* v_job_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1754_, v_job_1755_);
lean_dec_ref(v_ctx_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1758_, lean_object* v_ctx_1759_, lean_object* v_job_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1759_, v_job_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_ctx_1764_, lean_object* v_job_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1763_, v_ctx_1764_, v_job_1765_);
lean_dec_ref(v_ctx_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object* v_info_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lake_computeTextFileHash(v_info_1770_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = lean_io_metadata(v_info_1770_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1786_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1786_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1786_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_modified_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint64_t v___x_1782_; lean_object* v___x_1784_; 
v_modified_1779_ = lean_ctor_get(v_a_1775_, 1);
lean_inc_ref(v_modified_1779_);
lean_dec(v_a_1775_);
v___x_1780_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1781_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1781_, 0, v_info_1770_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
lean_ctor_set(v___x_1781_, 2, v_modified_1779_);
v___x_1782_ = lean_unbox_uint64(v_a_1773_);
lean_dec(v_a_1773_);
lean_ctor_set_uint64(v___x_1781_, sizeof(void*)*3, v___x_1782_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1781_);
v___x_1784_ = v___x_1777_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1781_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_a_1773_);
lean_dec_ref(v_info_1770_);
v_a_1787_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1774_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1774_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_info_1770_);
v_a_1795_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1772_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1772_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object* v_info_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object* v___x_1809_, lean_object* v_as_1810_, size_t v_sz_1811_, size_t v_i_1812_, lean_object* v_b_1813_){
_start:
{
lean_object* v_a_1816_; uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_lt(v_i_1812_, v_sz_1811_);
if (v___x_1820_ == 0)
{
lean_dec_ref(v___x_1809_);
return v_b_1813_;
}
else
{
lean_object* v_snd_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1844_; 
v_snd_1821_ = lean_ctor_get(v_b_1813_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_b_1813_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; 
v_unused_1845_ = lean_ctor_get(v_b_1813_, 0);
lean_dec(v_unused_1845_);
v___x_1823_ = v_b_1813_;
v_isShared_1824_ = v_isSharedCheck_1844_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_snd_1821_);
lean_dec(v_b_1813_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1844_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1825_ = lean_box(0);
v_a_1826_ = lean_array_uget_borrowed(v_as_1810_, v_i_1812_);
v___x_1827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0));
lean_inc_ref(v___x_1809_);
v___x_1828_ = l_Lake_joinRelative(v___x_1809_, v___x_1827_);
lean_inc(v_a_1826_);
v___x_1829_ = l_Lake_joinRelative(v___x_1828_, v_a_1826_);
v___x_1830_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v___x_1829_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l_Lake_BuildTrace_mix(v_snd_1821_, v_a_1831_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1832_);
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1834_ = v___x_1823_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v_a_1816_ = v___x_1834_;
goto v___jp_1815_;
}
}
else
{
lean_object* v_a_1836_; 
v_a_1836_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1830_, 1);
if (lean_obj_tag(v_a_1836_) == 11)
{
lean_object* v___x_1838_; 
lean_dec_ref_known(v_a_1836_, 2);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1838_ = v___x_1823_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_snd_1821_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
v_a_1816_ = v___x_1838_;
goto v___jp_1815_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec(v_a_1836_);
lean_dec_ref(v___x_1809_);
v___x_1840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1));
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1840_);
v___x_1842_ = v___x_1823_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_snd_1821_);
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
v___jp_1815_:
{
size_t v___x_1817_; size_t v___x_1818_; 
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_add(v_i_1812_, v___x_1817_);
v_i_1812_ = v___x_1818_;
v_b_1813_ = v_a_1816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object* v___x_1846_, lean_object* v_as_1847_, lean_object* v_sz_1848_, lean_object* v_i_1849_, lean_object* v_b_1850_, lean_object* v___y_1851_){
_start:
{
size_t v_sz_boxed_1852_; size_t v_i_boxed_1853_; lean_object* v_res_1854_; 
v_sz_boxed_1852_ = lean_unbox_usize(v_sz_1848_);
lean_dec(v_sz_1848_);
v_i_boxed_1853_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1846_, v_as_1847_, v_sz_boxed_1852_, v_i_boxed_1853_, v_b_1850_);
lean_dec_ref(v_as_1847_);
return v_res_1854_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1));
v___x_1858_ = l_Lake_BuildTrace_nil(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
return v___x_1875_;
}
}
static size_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1876_; size_t v_sz_1877_; 
v___x_1876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v_sz_1877_ = lean_array_size(v___x_1876_);
return v_sz_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t v_sz_1878_, size_t v_i_1879_, lean_object* v_bs_1880_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_usize_dec_lt(v_i_1879_, v_sz_1878_);
if (v___x_1882_ == 0)
{
return v_bs_1880_;
}
else
{
lean_object* v_v_1883_; lean_object* v_config_1884_; lean_object* v_dir_1885_; uint8_t v_bootstrap_1886_; lean_object* v_buildDir_1887_; lean_object* v___x_1888_; lean_object* v_bs_x27_1889_; lean_object* v_val_1891_; 
v_v_1883_ = lean_array_uget_borrowed(v_bs_1880_, v_i_1879_);
v_config_1884_ = lean_ctor_get(v_v_1883_, 6);
v_dir_1885_ = lean_ctor_get(v_v_1883_, 4);
lean_inc_ref(v_dir_1885_);
v_bootstrap_1886_ = lean_ctor_get_uint8(v_config_1884_, sizeof(void*)*28);
v_buildDir_1887_ = lean_ctor_get(v_config_1884_, 5);
lean_inc_ref(v_buildDir_1887_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v_bs_x27_1889_ = lean_array_uset(v_bs_1880_, v_i_1879_, v___x_1888_);
if (v_bootstrap_1886_ == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref(v_buildDir_1887_);
lean_dec_ref(v_dir_1885_);
v___x_1896_ = lean_box(0);
v_val_1891_ = v___x_1896_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; size_t v_sz_1903_; size_t v___x_1904_; lean_object* v___x_1905_; lean_object* v_fst_1906_; 
v___x_1897_ = l_System_FilePath_normalize(v_buildDir_1887_);
v___x_1898_ = l_Lake_joinRelative(v_dir_1885_, v___x_1897_);
v___x_1899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0));
v___x_1900_ = l_Lake_joinRelative(v___x_1898_, v___x_1899_);
v___x_1901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v___x_1902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8);
v_sz_1903_ = lean_usize_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9);
v___x_1904_ = ((size_t)0ULL);
lean_inc_ref(v___x_1900_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1900_, v___x_1901_, v_sz_1903_, v___x_1904_, v___x_1902_);
v_fst_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_fst_1906_);
if (lean_obj_tag(v_fst_1906_) == 0)
{
lean_object* v_snd_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
v_snd_1907_ = lean_ctor_get(v___x_1905_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1905_, 0);
lean_dec(v_unused_1916_);
v___x_1909_ = v___x_1905_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_snd_1907_);
lean_dec(v___x_1905_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1900_);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_snd_1907_);
v___x_1912_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
v_val_1891_ = v___x_1913_;
goto v___jp_1890_;
}
}
}
else
{
lean_object* v_val_1917_; 
lean_dec_ref(v___x_1905_);
lean_dec_ref(v___x_1900_);
v_val_1917_ = lean_ctor_get(v_fst_1906_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v_fst_1906_, 1);
v_val_1891_ = v_val_1917_;
goto v___jp_1890_;
}
}
v___jp_1890_:
{
size_t v___x_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_add(v_i_1879_, v___x_1892_);
v___x_1894_ = lean_array_uset(v_bs_x27_1889_, v_i_1879_, v_val_1891_);
v_i_1879_ = v___x_1893_;
v_bs_1880_ = v___x_1894_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object* v_sz_1918_, lean_object* v_i_1919_, lean_object* v_bs_1920_, lean_object* v___y_1921_){
_start:
{
size_t v_sz_boxed_1922_; size_t v_i_boxed_1923_; lean_object* v_res_1924_; 
v_sz_boxed_1922_ = lean_unbox_usize(v_sz_1918_);
lean_dec(v_sz_1918_);
v_i_boxed_1923_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_boxed_1922_, v_i_boxed_1923_, v_bs_1920_);
return v_res_1924_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = l_Lean_versionStringCore;
v___x_1927_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0));
v___x_1928_ = lean_string_append(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2));
v___x_1931_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1);
v___x_1932_ = lean_string_append(v___x_1931_, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_nat_to_int(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5(void){
_start:
{
uint32_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = 0;
v___x_1936_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4);
v___x_1937_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set_uint32(v___x_1937_, sizeof(void*)*1, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_unsigned_to_nat(16u);
v___x_1940_ = lean_mk_array(v___x_1939_, v___x_1938_);
return v___x_1940_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object* v_ws_1946_, lean_object* v_cfg_1947_, lean_object* v_jobs_1948_, lean_object* v_cancelTk_x3f_1949_){
_start:
{
lean_object* v___y_1952_; uint8_t v___y_1953_; uint8_t v___y_1954_; lean_object* v___y_1955_; uint8_t v___y_1956_; uint8_t v___y_1957_; lean_object* v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_1962_; lean_object* v_val_1963_; uint8_t v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; uint8_t v___y_1984_; uint8_t v___y_1985_; uint8_t v___y_1986_; lean_object* v___y_1987_; uint8_t v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v_val_1994_; uint8_t v___x_2020_; 
v___x_2020_ = l_System_Platform_isOSX;
if (v___x_2020_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_2021_; 
v_macosxDeploymentTarget_x3f_2021_ = lean_ctor_get(v_cfg_1947_, 4);
lean_inc(v_macosxDeploymentTarget_x3f_2021_);
v_val_1994_ = v_macosxDeploymentTarget_x3f_2021_;
goto v___jp_1993_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_2022_; 
v_macosxDeploymentTarget_x3f_2022_ = lean_ctor_get(v_cfg_1947_, 4);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_2022_) == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___y_2026_; 
v___x_2023_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8));
v___x_2024_ = lean_io_getenv(v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9));
v___y_2026_ = v___x_2028_;
goto v___jp_2025_;
}
else
{
lean_object* v_val_2029_; 
v_val_2029_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_val_2029_);
lean_dec_ref_known(v___x_2024_, 1);
v___y_2026_ = v_val_2029_;
goto v___jp_2025_;
}
v___jp_2025_:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___y_2026_);
v_val_1994_ = v___x_2027_;
goto v___jp_1993_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_2022_);
v_val_1994_ = v_macosxDeploymentTarget_x3f_2022_;
goto v___jp_1993_;
}
}
v___jp_1951_:
{
lean_object* v_lakeEnv_1964_; lean_object* v_packages_1965_; size_t v_sz_1966_; size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint64_t v___x_1971_; uint64_t v___x_1972_; uint64_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_lakeEnv_1964_ = lean_ctor_get(v_ws_1946_, 0);
v_packages_1965_ = lean_ctor_get(v_ws_1946_, 4);
v_sz_1966_ = lean_array_size(v_packages_1965_);
v___x_1967_ = ((size_t)0ULL);
lean_inc_ref(v_packages_1965_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_1966_, v___x_1967_, v_packages_1965_);
v___x_1969_ = lean_alloc_ctor(0, 5, 6);
lean_ctor_set(v___x_1969_, 0, v___y_1955_);
lean_ctor_set(v___x_1969_, 1, v___y_1961_);
lean_ctor_set(v___x_1969_, 2, v___y_1958_);
lean_ctor_set(v___x_1969_, 3, v___y_1952_);
lean_ctor_set(v___x_1969_, 4, v___y_1960_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*5, v___y_1962_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*5 + 1, v___y_1956_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*5 + 2, v___y_1959_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*5 + 3, v___y_1957_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*5 + 4, v___y_1953_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*5 + 5, v___y_1954_);
v___x_1970_ = l_Lake_Env_leanGithash(v_lakeEnv_1964_);
v___x_1971_ = l_Lake_Hash_nil;
v___x_1972_ = lean_string_hash(v___x_1970_);
v___x_1973_ = lean_uint64_mix_hash(v___x_1971_, v___x_1972_);
v___x_1974_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3);
v___x_1975_ = lean_string_append(v___x_1974_, v___x_1970_);
lean_dec_ref(v___x_1970_);
v___x_1976_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1977_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5);
v___x_1978_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1978_, 0, v___x_1975_);
lean_ctor_set(v___x_1978_, 1, v___x_1976_);
lean_ctor_set(v___x_1978_, 2, v___x_1977_);
lean_ctor_set_uint64(v___x_1978_, sizeof(void*)*3, v___x_1973_);
v___x_1979_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1969_);
lean_ctor_set(v___x_1979_, 1, v_ws_1946_);
lean_ctor_set(v___x_1979_, 2, v___x_1978_);
lean_ctor_set(v___x_1979_, 3, v___x_1968_);
lean_ctor_set(v___x_1979_, 4, v_jobs_1948_);
lean_ctor_set(v___x_1979_, 5, v_val_1963_);
lean_ctor_set(v___x_1979_, 6, v_cancelTk_x3f_1949_);
return v___x_1979_;
}
v___jp_1980_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_box(0);
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1981_;
v___y_1954_ = v___y_1984_;
v___y_1955_ = v___y_1983_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1986_;
v___y_1958_ = v___y_1987_;
v___y_1959_ = v___y_1988_;
v___y_1960_ = v___y_1989_;
v___y_1961_ = v___y_1990_;
v___y_1962_ = v___y_1991_;
v_val_1963_ = v___x_1992_;
goto v___jp_1951_;
}
v___jp_1993_:
{
lean_object* v_outputsFile_x3f_1995_; 
v_outputsFile_x3f_1995_ = lean_ctor_get(v_cfg_1947_, 1);
lean_inc(v_outputsFile_x3f_1995_);
if (lean_obj_tag(v_outputsFile_x3f_1995_) == 0)
{
lean_object* v_toLogConfig_1996_; uint8_t v_oldMode_1997_; uint8_t v_trustHash_1998_; uint8_t v_noBuild_1999_; uint8_t v_failFast_2000_; uint8_t v_verbosity_2001_; uint8_t v_showSuccess_2002_; lean_object* v_outputsIdx_2003_; lean_object* v_leanOptOverrides_2004_; 
v_toLogConfig_1996_ = lean_ctor_get(v_cfg_1947_, 0);
lean_inc_ref(v_toLogConfig_1996_);
v_oldMode_1997_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5);
v_trustHash_1998_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 1);
v_noBuild_1999_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 2);
v_failFast_2000_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 3);
v_verbosity_2001_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 4);
v_showSuccess_2002_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 5);
v_outputsIdx_2003_ = lean_ctor_get(v_cfg_1947_, 2);
lean_inc(v_outputsIdx_2003_);
v_leanOptOverrides_2004_ = lean_ctor_get(v_cfg_1947_, 3);
lean_inc(v_leanOptOverrides_2004_);
lean_dec_ref(v_cfg_1947_);
v___y_1981_ = v_verbosity_2001_;
v___y_1982_ = v_leanOptOverrides_2004_;
v___y_1983_ = v_toLogConfig_1996_;
v___y_1984_ = v_showSuccess_2002_;
v___y_1985_ = v_trustHash_1998_;
v___y_1986_ = v_failFast_2000_;
v___y_1987_ = v_outputsIdx_2003_;
v___y_1988_ = v_noBuild_1999_;
v___y_1989_ = v_val_1994_;
v___y_1990_ = v_outputsFile_x3f_1995_;
v___y_1991_ = v_oldMode_1997_;
goto v___jp_1980_;
}
else
{
lean_object* v_toLogConfig_2005_; uint8_t v_oldMode_2006_; uint8_t v_trustHash_2007_; uint8_t v_noBuild_2008_; uint8_t v_failFast_2009_; uint8_t v_verbosity_2010_; uint8_t v_showSuccess_2011_; lean_object* v_outputsIdx_2012_; lean_object* v_leanOptOverrides_2013_; lean_object* v_packages_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v_toLogConfig_2005_ = lean_ctor_get(v_cfg_1947_, 0);
lean_inc_ref(v_toLogConfig_2005_);
v_oldMode_2006_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5);
v_trustHash_2007_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 1);
v_noBuild_2008_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 2);
v_failFast_2009_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 3);
v_verbosity_2010_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 4);
v_showSuccess_2011_ = lean_ctor_get_uint8(v_cfg_1947_, sizeof(void*)*5 + 5);
v_outputsIdx_2012_ = lean_ctor_get(v_cfg_1947_, 2);
lean_inc(v_outputsIdx_2012_);
v_leanOptOverrides_2013_ = lean_ctor_get(v_cfg_1947_, 3);
lean_inc(v_leanOptOverrides_2013_);
lean_dec_ref(v_cfg_1947_);
v_packages_2014_ = lean_ctor_get(v_ws_1946_, 4);
v___x_2015_ = lean_array_get_size(v_packages_2014_);
v___x_2016_ = lean_nat_dec_lt(v_outputsIdx_2012_, v___x_2015_);
if (v___x_2016_ == 0)
{
v___y_1981_ = v_verbosity_2010_;
v___y_1982_ = v_leanOptOverrides_2013_;
v___y_1983_ = v_toLogConfig_2005_;
v___y_1984_ = v_showSuccess_2011_;
v___y_1985_ = v_trustHash_2007_;
v___y_1986_ = v_failFast_2009_;
v___y_1987_ = v_outputsIdx_2012_;
v___y_1988_ = v_noBuild_2008_;
v___y_1989_ = v_val_1994_;
v___y_1990_ = v_outputsFile_x3f_1995_;
v___y_1991_ = v_oldMode_2006_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7);
v___x_2018_ = lean_st_mk_ref(v___x_2017_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___y_1952_ = v_leanOptOverrides_2013_;
v___y_1953_ = v_verbosity_2010_;
v___y_1954_ = v_showSuccess_2011_;
v___y_1955_ = v_toLogConfig_2005_;
v___y_1956_ = v_trustHash_2007_;
v___y_1957_ = v_failFast_2009_;
v___y_1958_ = v_outputsIdx_2012_;
v___y_1959_ = v_noBuild_2008_;
v___y_1960_ = v_val_1994_;
v___y_1961_ = v_outputsFile_x3f_1995_;
v___y_1962_ = v_oldMode_2006_;
v_val_1963_ = v___x_2019_;
goto v___jp_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object* v_ws_2030_, lean_object* v_cfg_2031_, lean_object* v_jobs_2032_, lean_object* v_cancelTk_x3f_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2030_, v_cfg_2031_, v_jobs_2032_, v_cancelTk_x3f_2033_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_log_2044_; uint8_t v_action_2045_; uint8_t v_wantsRebuild_2046_; lean_object* v_trace_2047_; lean_object* v_buildTime_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2077_; 
v_log_2044_ = lean_ctor_get(v___y_2042_, 0);
v_action_2045_ = lean_ctor_get_uint8(v___y_2042_, sizeof(void*)*3);
v_wantsRebuild_2046_ = lean_ctor_get_uint8(v___y_2042_, sizeof(void*)*3 + 1);
v_trace_2047_ = lean_ctor_get(v___y_2042_, 1);
v_buildTime_2048_ = lean_ctor_get(v___y_2042_, 2);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___y_2042_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2050_ = v___y_2042_;
v_isShared_2051_ = v_isSharedCheck_2077_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_buildTime_2048_);
lean_inc(v_trace_2047_);
lean_inc(v_log_2044_);
lean_dec(v___y_2042_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2077_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_apply_7(v_build_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v_log_2044_, lean_box(0));
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2064_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_a_2054_ = lean_ctor_get(v___x_2052_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2056_ = v___x_2052_;
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v_a_2054_);
v___x_2059_ = v___x_2050_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2054_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_trace_2047_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_buildTime_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3, v_action_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 1, v_wantsRebuild_2046_);
v___x_2059_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2059_);
v___x_2061_ = v___x_2056_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2053_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2076_; 
v_a_2065_ = lean_ctor_get(v___x_2052_, 0);
v_a_2066_ = lean_ctor_get(v___x_2052_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2068_ = v___x_2052_;
v_isShared_2069_ = v_isSharedCheck_2076_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_inc(v_a_2065_);
lean_dec(v___x_2052_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2076_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v_a_2066_);
v___x_2071_ = v___x_2050_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2066_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_trace_2047_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_buildTime_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*3, v_action_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*3 + 1, v_wantsRebuild_2046_);
v___x_2071_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2071_);
v___x_2073_ = v___x_2068_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2065_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_2088_, lean_object* v_build_2089_, lean_object* v_caption_2090_){
_start:
{
lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___f_2092_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2092_, 0, v_build_2089_);
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_box(1);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_st_mk_ref(v___x_2096_);
v___x_2099_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_2100_ = l_Lake_Job_async___redArg(v___x_2093_, v___f_2092_, v___x_2094_, v_caption_2090_, v___x_2099_, v___x_2097_, v___x_2095_, v___x_2098_, v_bctx_2088_);
v___x_2101_ = lean_st_ref_get(v___x_2098_);
lean_dec(v___x_2098_);
lean_dec(v___x_2101_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_2102_, lean_object* v_build_2103_, lean_object* v_caption_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2102_, v_build_2103_, v_caption_2104_);
lean_dec_ref(v_bctx_2102_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_2107_, lean_object* v_bctx_2108_, lean_object* v_build_2109_, lean_object* v_caption_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2108_, v_build_2109_, v_caption_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_bctx_2114_, lean_object* v_build_2115_, lean_object* v_caption_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_2113_, v_bctx_2114_, v_build_2115_, v_caption_2116_);
lean_dec_ref(v_bctx_2114_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_2119_, uint8_t v___x_2120_, uint8_t v___x_2121_, lean_object* v_as_2122_, size_t v_i_2123_, size_t v_stop_2124_, lean_object* v_b_2125_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_eq(v_i_2123_, v_stop_2124_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; 
v___x_2128_ = lean_array_uget_borrowed(v_as_2122_, v_i_2123_);
lean_inc_ref(v___x_2119_);
v___x_2129_ = l_Lake_logToStream(v___x_2128_, v___x_2119_, v___x_2120_, v___x_2121_);
v___x_2130_ = ((size_t)1ULL);
v___x_2131_ = lean_usize_add(v_i_2123_, v___x_2130_);
v_i_2123_ = v___x_2131_;
v_b_2125_ = v___x_2129_;
goto _start;
}
else
{
lean_dec_ref(v___x_2119_);
return v_b_2125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_2133_, lean_object* v___x_2134_, lean_object* v___x_2135_, lean_object* v_as_2136_, lean_object* v_i_2137_, lean_object* v_stop_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_){
_start:
{
uint8_t v___x_1089__boxed_2141_; uint8_t v___x_1090__boxed_2142_; size_t v_i_boxed_2143_; size_t v_stop_boxed_2144_; lean_object* v_res_2145_; 
v___x_1089__boxed_2141_ = lean_unbox(v___x_2134_);
v___x_1090__boxed_2142_ = lean_unbox(v___x_2135_);
v_i_boxed_2143_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_stop_boxed_2144_ = lean_unbox_usize(v_stop_2138_);
lean_dec(v_stop_2138_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2133_, v___x_1089__boxed_2141_, v___x_1090__boxed_2142_, v_as_2136_, v_i_boxed_2143_, v_stop_boxed_2144_, v_b_2139_);
lean_dec_ref(v_as_2136_);
return v_res_2145_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v___x_2146_, lean_object* v___x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
if (lean_obj_tag(v_x_2149_) == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = 1;
return v___x_2150_;
}
else
{
uint8_t v___x_2151_; 
v___x_2151_ = 0;
return v___x_2151_;
}
}
else
{
if (lean_obj_tag(v_x_2149_) == 0)
{
uint8_t v___x_2152_; 
v___x_2152_ = 0;
return v___x_2152_;
}
else
{
lean_object* v_val_2153_; uint8_t v___x_2154_; 
v_val_2153_ = lean_ctor_get(v_x_2149_, 0);
v___x_2154_ = lean_unbox(v_val_2153_);
if (v___x_2154_ == 0)
{
lean_object* v_val_2155_; uint8_t v___x_2156_; 
v_val_2155_ = lean_ctor_get(v_x_2148_, 0);
v___x_2156_ = lean_unbox(v_val_2155_);
if (v___x_2156_ == 0)
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_nat_dec_lt(v___x_2146_, v___x_2147_);
return v___x_2157_;
}
else
{
uint8_t v___x_2158_; 
v___x_2158_ = lean_unbox(v_val_2153_);
return v___x_2158_;
}
}
else
{
lean_object* v_val_2159_; uint8_t v___x_2160_; 
v_val_2159_ = lean_ctor_get(v_x_2148_, 0);
v___x_2160_ = lean_unbox(v_val_2159_);
return v___x_2160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
uint8_t v_res_2165_; lean_object* v_r_2166_; 
v_res_2165_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v___x_2161_, v___x_2162_, v_x_2163_, v_x_2164_);
lean_dec(v_x_2164_);
lean_dec(v_x_2163_);
lean_dec(v___x_2162_);
lean_dec(v___x_2161_);
v_r_2166_ = lean_box(v_res_2165_);
return v_r_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_2167_, uint8_t v___x_2168_, uint8_t v___x_2169_, lean_object* v_bctx_2170_, lean_object* v_out_2171_, lean_object* v_outputsFile_2172_){
_start:
{
lean_object* v___y_2177_; lean_object* v___y_2178_; uint8_t v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v_outputsRef_x3f_2200_; 
v_outputsRef_x3f_2200_ = lean_ctor_get(v_bctx_2170_, 5);
lean_inc(v_outputsRef_x3f_2200_);
if (lean_obj_tag(v_outputsRef_x3f_2200_) == 1)
{
lean_object* v_toContext_2201_; lean_object* v_toBuildConfig_2202_; lean_object* v_val_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2320_; 
v_toContext_2201_ = lean_ctor_get(v_bctx_2170_, 1);
lean_inc(v_toContext_2201_);
v_toBuildConfig_2202_ = lean_ctor_get(v_bctx_2170_, 0);
lean_inc_ref(v_toBuildConfig_2202_);
lean_dec_ref(v_bctx_2170_);
v_val_2203_ = lean_ctor_get(v_outputsRef_x3f_2200_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_outputsRef_x3f_2200_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2205_ = v_outputsRef_x3f_2200_;
v_isShared_2206_ = v_isSharedCheck_2320_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_val_2203_);
lean_dec(v_outputsRef_x3f_2200_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2320_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_lakeEnv_2207_; lean_object* v_packages_2208_; uint8_t v_verbosity_2209_; lean_object* v_outputsIdx_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_lakeEnv_2207_ = lean_ctor_get(v_toContext_2201_, 0);
lean_inc_ref(v_lakeEnv_2207_);
v_packages_2208_ = lean_ctor_get(v_toContext_2201_, 4);
lean_inc_ref(v_packages_2208_);
lean_dec(v_toContext_2201_);
v_verbosity_2209_ = lean_ctor_get_uint8(v_toBuildConfig_2202_, sizeof(void*)*5 + 4);
v_outputsIdx_2210_ = lean_ctor_get(v_toBuildConfig_2202_, 2);
lean_inc(v_outputsIdx_2210_);
lean_dec_ref(v_toBuildConfig_2202_);
v___x_2211_ = lean_array_get_size(v_packages_2208_);
v___x_2212_ = lean_nat_dec_lt(v_outputsIdx_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v_putStr_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec(v_outputsIdx_2210_);
lean_dec_ref(v_packages_2208_);
lean_dec_ref(v_lakeEnv_2207_);
lean_del_object(v___x_2205_);
lean_dec(v_val_2203_);
lean_dec_ref(v_outputsFile_2172_);
lean_dec_ref(v___x_2167_);
v_putStr_2213_ = lean_ctor_get(v_out_2171_, 4);
lean_inc_ref(v_putStr_2213_);
lean_dec_ref(v_out_2171_);
v___x_2214_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__0));
v___x_2215_ = lean_apply_2(v_putStr_2213_, v___x_2214_, lean_box(0));
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_dec_ref_known(v___x_2215_, 1);
goto v___jp_2196_;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2218_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2219_ = lean_unsigned_to_nat(82u);
v___x_2220_ = lean_unsigned_to_nat(4u);
v___x_2221_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2222_ = lean_io_error_to_string(v_a_2216_);
v___x_2223_ = lean_string_append(v___x_2221_, v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__3);
v___x_2227_ = lean_string_append(v___x_2225_, v___x_2226_);
v___x_2228_ = l_mkPanicMessageWithDecl(v___x_2217_, v___x_2218_, v___x_2219_, v___x_2220_, v___x_2227_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2228_);
goto v___jp_2196_;
}
}
else
{
lean_object* v___x_2230_; uint8_t v___y_2232_; uint8_t v___y_2296_; uint8_t v___y_2305_; lean_object* v_config_2306_; lean_object* v_enableArtifactCache_x3f_2307_; 
v___x_2230_ = lean_array_fget(v_packages_2208_, v_outputsIdx_2210_);
v_config_2306_ = lean_ctor_get(v___x_2230_, 6);
v_enableArtifactCache_x3f_2307_ = lean_ctor_get(v_config_2306_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_2307_) == 0)
{
lean_object* v_enableArtifactCache_x3f_2308_; 
v_enableArtifactCache_x3f_2308_ = lean_ctor_get(v_lakeEnv_2207_, 6);
lean_inc(v_enableArtifactCache_x3f_2308_);
lean_dec_ref(v_lakeEnv_2207_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2308_) == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_config_2311_; lean_object* v_enableArtifactCache_x3f_2312_; 
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_array_fget(v_packages_2208_, v___x_2309_);
lean_dec_ref(v_packages_2208_);
v_config_2311_ = lean_ctor_get(v___x_2310_, 6);
lean_inc_ref(v_config_2311_);
lean_dec(v___x_2310_);
v_enableArtifactCache_x3f_2312_ = lean_ctor_get(v_config_2311_, 24);
lean_inc(v_enableArtifactCache_x3f_2312_);
lean_dec_ref(v_config_2311_);
if (lean_obj_tag(v_enableArtifactCache_x3f_2312_) == 0)
{
uint8_t v___x_2313_; 
v___x_2313_ = 0;
v___y_2296_ = v___x_2313_;
goto v___jp_2295_;
}
else
{
lean_object* v_val_2314_; uint8_t v___x_2315_; 
v_val_2314_ = lean_ctor_get(v_enableArtifactCache_x3f_2312_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2312_, 1);
v___x_2315_ = lean_unbox(v_val_2314_);
lean_dec(v_val_2314_);
v___y_2305_ = v___x_2315_;
goto v___jp_2304_;
}
}
else
{
lean_object* v_val_2316_; uint8_t v___x_2317_; 
lean_dec_ref(v_packages_2208_);
v_val_2316_ = lean_ctor_get(v_enableArtifactCache_x3f_2308_, 0);
lean_inc(v_val_2316_);
lean_dec_ref_known(v_enableArtifactCache_x3f_2308_, 1);
v___x_2317_ = lean_unbox(v_val_2316_);
lean_dec(v_val_2316_);
v___y_2305_ = v___x_2317_;
goto v___jp_2304_;
}
}
else
{
lean_object* v_val_2318_; uint8_t v___x_2319_; 
lean_dec_ref(v_packages_2208_);
lean_dec_ref(v_lakeEnv_2207_);
v_val_2318_ = lean_ctor_get(v_enableArtifactCache_x3f_2307_, 0);
v___x_2319_ = lean_unbox(v_val_2318_);
v___y_2305_ = v___x_2319_;
goto v___jp_2304_;
}
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v_config_2234_; lean_object* v_toLeanConfig_2235_; lean_object* v_platformIndependent_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2233_ = lean_st_ref_get(v_val_2203_);
lean_dec(v_val_2203_);
v_config_2234_ = lean_ctor_get(v___x_2230_, 6);
lean_inc_ref(v_config_2234_);
lean_dec(v___x_2230_);
v_toLeanConfig_2235_ = lean_ctor_get(v_config_2234_, 1);
lean_inc_ref(v_toLeanConfig_2235_);
lean_dec_ref(v_config_2234_);
v_platformIndependent_2236_ = lean_ctor_get(v_toLeanConfig_2235_, 10);
lean_inc(v_platformIndependent_2236_);
lean_dec_ref(v_toLeanConfig_2235_);
v___x_2237_ = lean_box(v___x_2212_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2237_);
v___x_2239_ = v___x_2205_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
uint8_t v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2240_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_outputsIdx_2210_, v___x_2211_, v_platformIndependent_2236_, v___x_2239_);
lean_dec_ref(v___x_2239_);
lean_dec(v_platformIndependent_2236_);
lean_dec(v_outputsIdx_2210_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__6));
v___x_2243_ = l_Lake_CacheMap_writeFile(v_outputsFile_2172_, v___x_2233_, v___x_2240_, v___x_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 2);
v___x_2245_ = lean_array_get_size(v_a_2244_);
v___x_2246_ = lean_nat_dec_eq(v___x_2245_, v___x_2241_);
if (v___x_2246_ == 0)
{
if (v___y_2232_ == 0)
{
lean_dec(v_a_2244_);
lean_dec_ref(v_out_2171_);
lean_dec_ref(v___x_2167_);
goto v___jp_2174_;
}
else
{
lean_object* v_putStr_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_putStr_2247_ = lean_ctor_get(v_out_2171_, 4);
lean_inc_ref(v_putStr_2247_);
lean_dec_ref(v_out_2171_);
v___x_2248_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__7));
v___x_2249_ = lean_apply_2(v_putStr_2247_, v___x_2248_, lean_box(0));
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_dec_ref_known(v___x_2249_, 1);
v___y_2177_ = v___x_2241_;
v___y_2178_ = v_a_2244_;
goto v___jp_2176_;
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2252_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2253_ = lean_unsigned_to_nat(82u);
v___x_2254_ = lean_unsigned_to_nat(4u);
v___x_2255_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2256_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2257_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2256_, v___y_2232_);
v___x_2258_ = lean_string_append(v___x_2255_, v___x_2257_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2260_ = lean_string_append(v___x_2258_, v___x_2259_);
v___x_2261_ = lean_io_error_to_string(v_a_2250_);
v___x_2262_ = lean_string_append(v___x_2260_, v___x_2261_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__10);
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
v___x_2267_ = l_mkPanicMessageWithDecl(v___x_2251_, v___x_2252_, v___x_2253_, v___x_2254_, v___x_2266_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2267_);
v___y_2177_ = v___x_2241_;
v___y_2178_ = v_a_2244_;
goto v___jp_2176_;
}
}
}
else
{
lean_dec(v_a_2244_);
lean_dec_ref(v_out_2171_);
lean_dec_ref(v___x_2167_);
goto v___jp_2174_;
}
}
else
{
lean_object* v_a_2269_; lean_object* v_putStr_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_a_2269_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2243_, 2);
v_putStr_2270_ = lean_ctor_get(v_out_2171_, 4);
lean_inc_ref(v_putStr_2270_);
lean_dec_ref(v_out_2171_);
v___x_2271_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__11));
v___x_2272_ = lean_apply_2(v_putStr_2270_, v___x_2271_, lean_box(0));
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec_ref_known(v___x_2272_, 1);
v___y_2186_ = v___y_2232_;
v___y_2187_ = v_a_2269_;
v___y_2188_ = v___x_2241_;
goto v___jp_2185_;
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2275_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2276_ = lean_unsigned_to_nat(82u);
v___x_2277_ = lean_unsigned_to_nat(4u);
v___x_2278_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2279_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2280_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2279_, v___x_2212_);
v___x_2281_ = lean_string_append(v___x_2278_, v___x_2280_);
lean_dec_ref(v___x_2280_);
v___x_2282_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2283_ = lean_string_append(v___x_2281_, v___x_2282_);
v___x_2284_ = lean_io_error_to_string(v_a_2273_);
v___x_2285_ = lean_string_append(v___x_2283_, v___x_2284_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2287_ = lean_string_append(v___x_2285_, v___x_2286_);
v___x_2288_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__14);
v___x_2289_ = lean_string_append(v___x_2287_, v___x_2288_);
v___x_2290_ = l_mkPanicMessageWithDecl(v___x_2274_, v___x_2275_, v___x_2276_, v___x_2277_, v___x_2289_);
lean_dec_ref(v___x_2289_);
v___x_2291_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2290_);
v___y_2186_ = v___y_2232_;
v___y_2187_ = v_a_2269_;
v___y_2188_ = v___x_2241_;
goto v___jp_2185_;
}
}
}
}
v___jp_2293_:
{
if (v_verbosity_2209_ == 2)
{
v___y_2232_ = v___x_2212_;
goto v___jp_2231_;
}
else
{
uint8_t v___x_2294_; 
v___x_2294_ = 0;
v___y_2232_ = v___x_2294_;
goto v___jp_2231_;
}
}
v___jp_2295_:
{
lean_object* v_baseName_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_baseName_2297_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_baseName_2297_);
v___x_2298_ = l_Lean_Name_toString(v_baseName_2297_, v___y_2296_);
v___x_2299_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__15));
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
v___x_2301_ = 2;
v___x_2302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*1, v___x_2301_);
lean_inc_ref(v___x_2167_);
v___x_2303_ = l_Lake_logToStream(v___x_2302_, v___x_2167_, v___x_2168_, v___x_2169_);
lean_dec_ref_known(v___x_2302_, 1);
goto v___jp_2293_;
}
v___jp_2304_:
{
if (v___y_2305_ == 0)
{
v___y_2296_ = v___y_2305_;
goto v___jp_2295_;
}
else
{
goto v___jp_2293_;
}
}
}
}
}
else
{
lean_object* v_putStr_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_outputsRef_x3f_2200_);
lean_dec_ref(v_outputsFile_2172_);
lean_dec_ref(v_bctx_2170_);
lean_dec_ref(v___x_2167_);
v_putStr_2321_ = lean_ctor_get(v_out_2171_, 4);
lean_inc_ref(v_putStr_2321_);
lean_dec_ref(v_out_2171_);
v___x_2322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__16));
v___x_2323_ = lean_apply_2(v_putStr_2321_, v___x_2322_, lean_box(0));
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_dec_ref_known(v___x_2323_, 1);
goto v___jp_2198_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2326_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2327_ = lean_unsigned_to_nat(82u);
v___x_2328_ = lean_unsigned_to_nat(4u);
v___x_2329_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2330_ = lean_io_error_to_string(v_a_2324_);
v___x_2331_ = lean_string_append(v___x_2329_, v___x_2330_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2333_ = lean_string_append(v___x_2331_, v___x_2332_);
v___x_2334_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19, &l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___closed__19);
v___x_2335_ = lean_string_append(v___x_2333_, v___x_2334_);
v___x_2336_ = l_mkPanicMessageWithDecl(v___x_2325_, v___x_2326_, v___x_2327_, v___x_2328_, v___x_2335_);
lean_dec_ref(v___x_2335_);
v___x_2337_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2336_);
goto v___jp_2198_;
}
}
v___jp_2174_:
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_box(0);
return v___x_2175_;
}
v___jp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2179_ = lean_array_get_size(v___y_2178_);
v___x_2180_ = lean_box(0);
v___x_2181_ = lean_nat_dec_lt(v___y_2177_, v___x_2179_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v___y_2178_);
lean_dec_ref(v___x_2167_);
return v___x_2180_;
}
else
{
size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = lean_usize_of_nat(v___x_2179_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2167_, v___x_2168_, v___x_2169_, v___y_2178_, v___x_2182_, v___x_2183_, v___x_2180_);
lean_dec_ref(v___y_2178_);
return v___x_2184_;
}
}
v___jp_2185_:
{
if (v___y_2186_ == 0)
{
lean_object* v___x_2189_; 
lean_dec_ref(v___y_2187_);
lean_dec_ref(v___x_2167_);
v___x_2189_ = lean_box(0);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = lean_array_get_size(v___y_2187_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_nat_dec_lt(v___y_2188_, v___x_2190_);
if (v___x_2192_ == 0)
{
lean_dec_ref(v___y_2187_);
lean_dec_ref(v___x_2167_);
return v___x_2191_;
}
else
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((size_t)0ULL);
v___x_2194_ = lean_usize_of_nat(v___x_2190_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2167_, v___x_2168_, v___x_2169_, v___y_2187_, v___x_2193_, v___x_2194_, v___x_2191_);
lean_dec_ref(v___y_2187_);
return v___x_2195_;
}
}
}
v___jp_2196_:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
v___jp_2198_:
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_box(0);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v_bctx_2341_, lean_object* v_out_2342_, lean_object* v_outputsFile_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v___x_1333__boxed_2345_; uint8_t v___x_1334__boxed_2346_; lean_object* v_res_2347_; 
v___x_1333__boxed_2345_ = lean_unbox(v___x_2339_);
v___x_1334__boxed_2346_ = lean_unbox(v___x_2340_);
v_res_2347_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2338_, v___x_1333__boxed_2345_, v___x_1334__boxed_2346_, v_bctx_2341_, v_out_2342_, v_outputsFile_2343_);
return v_res_2347_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = 3;
v___x_2349_ = lean_uint32_to_uint8(v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2350_, lean_object* v_bctx_2351_, lean_object* v_mctx_2352_, lean_object* v_result_2353_){
_start:
{
lean_object* v___y_2356_; lean_object* v_out_2359_; uint8_t v_outLv_2360_; uint8_t v_useAnsi_2361_; lean_object* v_toMonitorResult_2362_; lean_object* v_out_2363_; lean_object* v___x_2379_; lean_object* v_outputsFile_x3f_2380_; 
v_out_2359_ = lean_ctor_get(v_mctx_2352_, 1);
lean_inc_ref_n(v_out_2359_, 2);
v_outLv_2360_ = lean_ctor_get_uint8(v_mctx_2352_, sizeof(void*)*4);
v_useAnsi_2361_ = lean_ctor_get_uint8(v_mctx_2352_, sizeof(void*)*4 + 4);
lean_dec_ref(v_mctx_2352_);
v_toMonitorResult_2362_ = lean_ctor_get(v_result_2353_, 0);
lean_inc_ref_n(v_toMonitorResult_2362_, 2);
v_out_2363_ = lean_ctor_get(v_result_2353_, 1);
lean_inc_ref(v_out_2363_);
lean_dec_ref(v_result_2353_);
v___x_2379_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2350_, v_out_2359_, v_toMonitorResult_2362_);
v_outputsFile_x3f_2380_ = lean_ctor_get(v_cfg_2350_, 1);
if (lean_obj_tag(v_outputsFile_x3f_2380_) == 1)
{
lean_object* v_val_2381_; lean_object* v___x_2382_; 
v_val_2381_ = lean_ctor_get(v_outputsFile_x3f_2380_, 0);
lean_inc(v_val_2381_);
lean_inc_ref(v_out_2359_);
v___x_2382_ = l___private_Lake_Build_Run_0__Lake_BuildContext_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2359_, v_outLv_2360_, v_useAnsi_2361_, v_bctx_2351_, v_out_2359_, v_val_2381_);
goto v___jp_2364_;
}
else
{
lean_dec_ref(v_out_2359_);
lean_dec_ref(v_bctx_2351_);
goto v___jp_2364_;
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_mk_io_user_error(v___y_2356_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
v___jp_2364_:
{
if (lean_obj_tag(v_out_2363_) == 0)
{
uint8_t v_noBuild_2365_; 
v_noBuild_2365_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*5 + 2);
lean_dec_ref(v_cfg_2350_);
if (v_noBuild_2365_ == 0)
{
lean_object* v_a_2366_; 
lean_dec_ref(v_toMonitorResult_2362_);
v_a_2366_ = lean_ctor_get(v_out_2363_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v_out_2363_, 1);
v___y_2356_ = v_a_2366_;
goto v___jp_2355_;
}
else
{
uint8_t v_wantsRebuild_2367_; 
v_wantsRebuild_2367_ = lean_ctor_get_uint8(v_toMonitorResult_2362_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2362_);
if (v_wantsRebuild_2367_ == 0)
{
lean_object* v_a_2368_; 
v_a_2368_ = lean_ctor_get(v_out_2363_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v_out_2363_, 1);
v___y_2356_ = v_a_2368_;
goto v___jp_2355_;
}
else
{
uint8_t v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref_known(v_out_2363_, 1);
v___x_2369_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2370_ = lean_io_exit(v___x_2369_);
return v___x_2370_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v_toMonitorResult_2362_);
lean_dec_ref(v_cfg_2350_);
v_a_2371_ = lean_ctor_get(v_out_2363_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_out_2363_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v_out_2363_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v_out_2363_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set_tag(v___x_2373_, 0);
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2383_, lean_object* v_bctx_2384_, lean_object* v_mctx_2385_, lean_object* v_result_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2383_, v_bctx_2384_, v_mctx_2385_, v_result_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2389_, lean_object* v_cfg_2390_, lean_object* v_bctx_2391_, lean_object* v_mctx_2392_, lean_object* v_result_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2390_, v_bctx_2391_, v_mctx_2392_, v_result_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_cfg_2397_, lean_object* v_bctx_2398_, lean_object* v_mctx_2399_, lean_object* v_result_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2396_, v_cfg_2397_, v_bctx_2398_, v_mctx_2399_, v_result_2400_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2403_, lean_object* v_build_2404_, lean_object* v_cfg_2405_, lean_object* v_caption_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v_cancelTk_x3f_2411_; uint8_t v_failFast_2417_; 
v___x_2408_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2409_ = lean_st_mk_ref(v___x_2408_);
v_failFast_2417_ = lean_ctor_get_uint8(v_cfg_2405_, sizeof(void*)*5 + 3);
if (v_failFast_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_box(0);
v_cancelTk_x3f_2411_ = v___x_2418_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = l_IO_CancelToken_new();
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
v_cancelTk_x3f_2411_ = v___x_2420_;
goto v___jp_2410_;
}
v___jp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_inc(v_cancelTk_x3f_2411_);
lean_inc(v___x_2409_);
v___x_2412_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2405_, v___x_2409_, v_cancelTk_x3f_2411_);
lean_inc_ref(v_cfg_2405_);
v___x_2413_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2403_, v_cfg_2405_, v___x_2409_, v_cancelTk_x3f_2411_);
v___x_2414_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2413_, v_build_2404_, v_caption_2406_);
v___x_2415_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2412_, v___x_2414_);
v___x_2416_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2405_, v___x_2413_, v___x_2412_, v___x_2415_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2421_, lean_object* v_build_2422_, lean_object* v_cfg_2423_, lean_object* v_caption_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2421_, v_build_2422_, v_cfg_2423_, v_caption_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2427_, lean_object* v_ws_2428_, lean_object* v_build_2429_, lean_object* v_cfg_2430_, lean_object* v_caption_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2428_, v_build_2429_, v_cfg_2430_, v_caption_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_ws_2435_, lean_object* v_build_2436_, lean_object* v_cfg_2437_, lean_object* v_caption_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2434_, v_ws_2435_, v_build_2436_, v_cfg_2437_, v_caption_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2444_, lean_object* v_job_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v_out_2448_; 
v___x_2447_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2444_, v_job_2445_);
v_out_2448_ = lean_ctor_get(v___x_2447_, 1);
lean_inc_ref(v_out_2448_);
if (lean_obj_tag(v_out_2448_) == 0)
{
lean_object* v_toMonitorResult_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2464_; 
v_toMonitorResult_2449_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2447_, 1);
lean_dec(v_unused_2465_);
v___x_2451_ = v___x_2447_;
v_isShared_2452_ = v_isSharedCheck_2464_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_toMonitorResult_2449_);
lean_dec(v___x_2447_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2464_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2463_; 
v_a_2453_ = lean_ctor_get(v_out_2448_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_out_2448_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2455_ = v_out_2448_;
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v_out_2448_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2460_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2458_);
v___x_2460_ = v___x_2451_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_toMonitorResult_2449_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2489_; 
v_a_2466_ = lean_ctor_get(v_out_2448_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_out_2448_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2468_ = v_out_2448_;
v_isShared_2469_ = v_isSharedCheck_2489_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v_out_2448_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2489_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v_toMonitorResult_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2487_; 
v_toMonitorResult_2470_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2447_, 1);
lean_dec(v_unused_2488_);
v___x_2472_ = v___x_2447_;
v_isShared_2473_ = v_isSharedCheck_2487_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_toMonitorResult_2470_);
lean_dec(v___x_2447_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2487_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_task_2474_; lean_object* v___x_2475_; 
v_task_2474_ = lean_ctor_get(v_a_2466_, 0);
lean_inc_ref(v_task_2474_);
lean_dec(v_a_2466_);
v___x_2475_ = lean_io_wait(v_task_2474_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 2);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v_a_2476_);
v___x_2478_ = v___x_2468_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2478_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2480_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v___x_2478_);
v___x_2480_ = v___x_2472_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_toMonitorResult_2470_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2475_, 2);
lean_del_object(v___x_2468_);
v___x_2483_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v___x_2483_);
v___x_2485_ = v___x_2472_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_toMonitorResult_2470_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2490_, lean_object* v_job_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2490_, v_job_2491_);
lean_dec_ref(v_mctx_2490_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2494_, lean_object* v_mctx_2495_, lean_object* v_job_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2495_, v_job_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2499_, lean_object* v_mctx_2500_, lean_object* v_job_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2499_, v_mctx_2500_, v_job_2501_);
lean_dec_ref(v_mctx_2500_);
return v_res_2503_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2518_, lean_object* v_build_2519_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_out_2532_; 
v___x_2521_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2522_ = lean_st_mk_ref(v___x_2521_);
v___x_2523_ = 0;
v___x_2524_ = 1;
v___x_2525_ = lean_box(0);
v___x_2526_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2522_);
v___x_2527_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2526_, v___x_2522_, v___x_2525_);
v___x_2528_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2518_, v___x_2526_, v___x_2522_, v___x_2525_);
v___x_2529_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2530_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2528_, v_build_2519_, v___x_2529_);
lean_dec_ref(v___x_2528_);
v___x_2531_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2527_, v___x_2530_);
lean_dec_ref(v___x_2527_);
v_out_2532_ = lean_ctor_get(v___x_2531_, 1);
lean_inc_ref(v_out_2532_);
lean_dec_ref(v___x_2531_);
if (lean_obj_tag(v_out_2532_) == 0)
{
lean_dec_ref_known(v_out_2532_, 1);
return v___x_2523_;
}
else
{
lean_dec_ref_known(v_out_2532_, 1);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2533_, lean_object* v_build_2534_, lean_object* v_a_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2533_, v_build_2534_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2538_, lean_object* v_ws_2539_, lean_object* v_build_2540_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2539_, v_build_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2543_, lean_object* v_ws_2544_, lean_object* v_build_2545_, lean_object* v_a_2546_){
_start:
{
uint8_t v_res_2547_; lean_object* v_r_2548_; 
v_res_2547_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2543_, v_ws_2544_, v_build_2545_);
v_r_2548_ = lean_box(v_res_2547_);
return v_r_2548_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2549_, lean_object* v_build_2550_, lean_object* v_cfg_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_cancelTk_x3f_2556_; uint8_t v_failFast_2563_; 
v___x_2553_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2554_ = lean_st_mk_ref(v___x_2553_);
v_failFast_2563_ = lean_ctor_get_uint8(v_cfg_2551_, sizeof(void*)*5 + 3);
if (v_failFast_2563_ == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_box(0);
v_cancelTk_x3f_2556_ = v___x_2564_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = l_IO_CancelToken_new();
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
v_cancelTk_x3f_2556_ = v___x_2566_;
goto v___jp_2555_;
}
v___jp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_inc(v_cancelTk_x3f_2556_);
lean_inc(v___x_2554_);
v___x_2557_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2551_, v___x_2554_, v_cancelTk_x3f_2556_);
lean_inc_ref(v_cfg_2551_);
v___x_2558_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2549_, v_cfg_2551_, v___x_2554_, v_cancelTk_x3f_2556_);
v___x_2559_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2560_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2558_, v_build_2550_, v___x_2559_);
v___x_2561_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2557_, v___x_2560_);
v___x_2562_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2551_, v___x_2558_, v___x_2557_, v___x_2561_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2567_, lean_object* v_build_2568_, lean_object* v_cfg_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lake_Workspace_runBuild___redArg(v_ws_2567_, v_build_2568_, v_cfg_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2572_, lean_object* v_ws_2573_, lean_object* v_build_2574_, lean_object* v_cfg_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lake_Workspace_runBuild___redArg(v_ws_2573_, v_build_2574_, v_cfg_2575_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2578_, lean_object* v_ws_2579_, lean_object* v_build_2580_, lean_object* v_cfg_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lake_Workspace_runBuild(v_00_u03b1_2578_, v_ws_2579_, v_build_2580_, v_cfg_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2584_, lean_object* v_cfg_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v___x_2588_; 
lean_inc(v_a_2586_);
v___x_2588_ = l_Lake_Workspace_runBuild___redArg(v_a_2586_, v_build_2584_, v_cfg_2585_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2589_, lean_object* v_cfg_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lake_runBuild___redArg(v_build_2589_, v_cfg_2590_, v_a_2591_);
lean_dec(v_a_2591_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2594_, lean_object* v_build_2595_, lean_object* v_cfg_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v___x_2599_; 
lean_inc(v_a_2597_);
v___x_2599_ = l_Lake_Workspace_runBuild___redArg(v_a_2597_, v_build_2595_, v_cfg_2596_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2600_, lean_object* v_build_2601_, lean_object* v_cfg_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lake_runBuild(v_00_u03b1_2600_, v_build_2601_, v_cfg_2602_, v_a_2603_);
lean_dec(v_a_2603_);
return v_res_2605_;
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
