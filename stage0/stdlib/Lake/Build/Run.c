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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value;
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value)} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_value;
static const lean_array_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = ": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16_value;
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
static const lean_ctor_object l_Lake_Workspace_checkNoBuild___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 1, 0, 0, 0)}};
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
lean_object* v_putStr_136_; lean_object* v___x_137_; 
v_putStr_136_ = lean_ctor_get(v_out_133_, 4);
lean_inc_ref(v_putStr_136_);
lean_dec_ref(v_out_133_);
lean_inc_ref(v_s_134_);
v___x_137_ = lean_apply_2(v_putStr_136_, v_s_134_, lean_box(0));
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; 
lean_dec_ref(v_s_134_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
return v_a_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_164_; 
v_a_139_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_164_ == 0)
{
v___x_141_ = v___x_137_;
v_isShared_142_ = v_isSharedCheck_164_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_164_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_143_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_144_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_145_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_146_ = lean_unsigned_to_nat(82u);
v___x_147_ = lean_unsigned_to_nat(4u);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_150_ = lean_io_error_to_string(v_a_139_);
v___x_151_ = lean_string_append(v___x_149_, v___x_150_);
lean_dec_ref(v___x_150_);
v___x_152_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_153_ = lean_string_append(v___x_151_, v___x_152_);
v___x_154_ = l_String_quote(v_s_134_);
if (v_isShared_142_ == 0)
{
lean_ctor_set_tag(v___x_141_, 3);
lean_ctor_set(v___x_141_, 0, v___x_154_);
v___x_156_ = v___x_141_;
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
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_181__overap_161_; lean_object* v___x_162_; 
v___x_157_ = l_Std_Format_defWidth;
v___x_158_ = l_Std_Format_pretty(v___x_156_, v___x_157_, v___x_148_, v___x_148_);
v___x_159_ = lean_string_append(v___x_153_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l_mkPanicMessageWithDecl(v___x_144_, v___x_145_, v___x_146_, v___x_147_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_181__overap_161_ = l_panic___redArg(v___x_143_, v___x_160_);
v___x_162_ = lean_apply_1(v___x_181__overap_161_, lean_box(0));
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
lean_object* v_val_174_; lean_object* v_out_176_; lean_object* v_putStr_177_; lean_object* v___x_178_; 
v_out_176_ = lean_ctor_get(v_a_170_, 1);
v_putStr_177_ = lean_ctor_get(v_out_176_, 4);
lean_inc_ref(v_putStr_177_);
lean_inc_ref(v_s_169_);
v___x_178_ = lean_apply_2(v_putStr_177_, v_s_169_, lean_box(0));
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; 
lean_dec_ref(v_s_169_);
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v_val_174_ = v_a_179_;
goto v___jp_173_;
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_205_; 
v_a_180_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_205_ == 0)
{
v___x_182_ = v___x_178_;
v_isShared_183_ = v_isSharedCheck_205_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_178_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_205_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_184_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_185_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_186_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_187_ = lean_unsigned_to_nat(82u);
v___x_188_ = lean_unsigned_to_nat(4u);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_191_ = lean_io_error_to_string(v_a_180_);
v___x_192_ = lean_string_append(v___x_190_, v___x_191_);
lean_dec_ref(v___x_191_);
v___x_193_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = l_String_quote(v_s_169_);
if (v_isShared_183_ == 0)
{
lean_ctor_set_tag(v___x_182_, 3);
lean_ctor_set(v___x_182_, 0, v___x_195_);
v___x_197_ = v___x_182_;
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
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_645__overap_202_; lean_object* v___x_203_; 
v___x_198_ = l_Std_Format_defWidth;
v___x_199_ = l_Std_Format_pretty(v___x_197_, v___x_198_, v___x_189_, v___x_189_);
v___x_200_ = lean_string_append(v___x_194_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_mkPanicMessageWithDecl(v___x_185_, v___x_186_, v___x_187_, v___x_188_, v___x_200_);
lean_dec_ref(v___x_200_);
v___x_645__overap_202_ = l_panic___redArg(v___x_184_, v___x_201_);
v___x_203_ = lean_apply_1(v___x_645__overap_202_, lean_box(0));
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
uint8_t v___y_13791__boxed_423_; uint8_t v_useAnsi_13792__boxed_424_; size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v___y_13791__boxed_423_ = lean_unbox(v___y_415_);
v_useAnsi_13792__boxed_424_ = lean_unbox(v_useAnsi_416_);
v_i_boxed_425_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_414_, v___y_13791__boxed_423_, v_useAnsi_13792__boxed_424_, v_as_417_, v_i_boxed_425_, v_stop_boxed_426_, v_b_420_, v___y_421_);
lean_dec_ref(v_as_417_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_444_; lean_object* v_val_445_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_jobNo_455_; lean_object* v_totalJobs_456_; uint8_t v_wantsRebuild_457_; lean_object* v_failures_458_; lean_object* v_resetCtrl_459_; lean_object* v_lastUpdate_460_; lean_object* v_spinnerIdx_461_; lean_object* v_out_462_; uint8_t v_outLv_463_; uint8_t v_failLv_464_; uint8_t v_minAction_465_; uint8_t v_showOptional_466_; uint8_t v_useAnsi_467_; uint8_t v_showProgress_468_; uint8_t v_showTime_469_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___y_476_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; uint8_t v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; uint8_t v___y_562_; lean_object* v___y_563_; uint8_t v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v_task_568_; lean_object* v_caption_569_; uint8_t v_optional_570_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; uint8_t v___y_575_; uint8_t v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; uint32_t v___y_580_; lean_object* v___y_581_; uint8_t v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; uint32_t v___y_615_; lean_object* v___y_616_; uint8_t v___y_617_; uint8_t v___y_618_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; uint8_t v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; uint32_t v___y_629_; lean_object* v___y_630_; uint8_t v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_641_; lean_object* v___y_642_; uint8_t v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; uint8_t v___y_648_; uint8_t v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; uint32_t v___y_652_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; uint8_t v___y_662_; uint8_t v___y_663_; uint8_t v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; uint8_t v___y_676_; uint8_t v___y_677_; uint8_t v___y_678_; uint8_t v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; uint8_t v___y_688_; uint8_t v___y_689_; uint8_t v___y_690_; uint8_t v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; uint8_t v___y_716_; uint8_t v___y_717_; uint8_t v___y_718_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; lean_object* v___y_737_; lean_object* v___y_738_; uint8_t v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; uint8_t v___y_742_; uint8_t v___y_743_; uint8_t v___y_744_; lean_object* v___y_745_; uint8_t v___y_746_; lean_object* v___y_751_; uint8_t v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; uint8_t v___y_755_; uint8_t v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_765_; lean_object* v___y_766_; uint8_t v___y_767_; lean_object* v___y_768_; uint8_t v___y_769_; uint8_t v___y_770_; lean_object* v___y_771_; uint8_t v___y_772_; lean_object* v___y_777_; lean_object* v___x_788_; lean_object* v_a_789_; 
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
v___x_788_ = lean_task_get_own(v_task_568_);
v_a_789_ = lean_ctor_get(v___x_788_, 1);
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___y_777_ = v_a_789_;
goto v___jp_776_;
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
v___x_477_ = lean_nat_dec_lt(v___y_471_, v___y_472_);
lean_dec(v___y_471_);
if (v___x_477_ == 0)
{
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
v___y_448_ = v___y_475_;
v___y_449_ = v___y_474_;
goto v___jp_447_;
}
else
{
lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v_snd_482_; 
v___x_478_ = lean_box(0);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___y_472_);
lean_dec(v___y_472_);
lean_inc_ref(v_out_462_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_462_, v___y_476_, v_useAnsi_467_, v___y_473_, v___x_479_, v___x_480_, v___x_478_, v___y_474_);
lean_dec_ref(v___y_473_);
v_snd_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_snd_482_);
lean_dec_ref(v___x_481_);
v___y_448_ = v___y_475_;
v___y_449_ = v_snd_482_;
goto v___jp_447_;
}
}
v___jp_483_:
{
if (v___y_486_ == 0)
{
lean_dec_ref(v___y_487_);
lean_dec(v___y_485_);
lean_dec(v___y_484_);
v___y_448_ = v___y_490_;
v___y_449_ = v___y_489_;
goto v___jp_447_;
}
else
{
if (v___y_488_ == 0)
{
v___y_471_ = v___y_484_;
v___y_472_ = v___y_485_;
v___y_473_ = v___y_487_;
v___y_474_ = v___y_489_;
v___y_475_ = v___y_490_;
v___y_476_ = v_outLv_463_;
goto v___jp_470_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = 0;
v___y_471_ = v___y_484_;
v___y_472_ = v___y_485_;
v___y_473_ = v___y_487_;
v___y_474_ = v___y_489_;
v___y_475_ = v___y_490_;
v___y_476_ = v___x_491_;
goto v___jp_470_;
}
}
}
v___jp_492_:
{
lean_object* v_out_502_; lean_object* v_jobNo_503_; lean_object* v_totalJobs_504_; uint8_t v_wantsRebuild_505_; lean_object* v_failures_506_; lean_object* v_resetCtrl_507_; lean_object* v_lastUpdate_508_; lean_object* v_spinnerIdx_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_555_; 
v_out_502_ = lean_ctor_get(v___y_500_, 1);
v_jobNo_503_ = lean_ctor_get(v___y_496_, 0);
v_totalJobs_504_ = lean_ctor_get(v___y_496_, 1);
v_wantsRebuild_505_ = lean_ctor_get_uint8(v___y_496_, sizeof(void*)*6);
v_failures_506_ = lean_ctor_get(v___y_496_, 2);
v_resetCtrl_507_ = lean_ctor_get(v___y_496_, 3);
v_lastUpdate_508_ = lean_ctor_get(v___y_496_, 4);
v_spinnerIdx_509_ = lean_ctor_get(v___y_496_, 5);
v_isSharedCheck_555_ = !lean_is_exclusive(v___y_496_);
if (v_isSharedCheck_555_ == 0)
{
v___x_511_ = v___y_496_;
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
lean_dec(v___y_496_);
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
v___y_487_ = v___y_497_;
v___y_488_ = v___y_499_;
v___y_489_ = v___x_516_;
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
lean_inc(v___y_493_);
v___x_532_ = l_Lean_Name_num___override(v___x_531_, v___y_493_);
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
lean_inc_n(v___y_493_, 2);
v___x_548_ = l_Std_Format_pretty(v___x_546_, v___x_547_, v___y_493_, v___y_493_);
v___x_549_ = lean_string_append(v___x_543_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_mkPanicMessageWithDecl(v___x_525_, v___x_526_, v___x_527_, v___x_528_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_550_);
v___y_484_ = v___y_493_;
v___y_485_ = v___y_494_;
v___y_486_ = v___y_495_;
v___y_487_ = v___y_497_;
v___y_488_ = v___y_499_;
v___y_489_ = v___x_516_;
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
v___x_567_ = l_Lake_Ansi_chalk(v___y_566_, v___y_563_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v___y_566_);
v___y_493_ = v___y_557_;
v___y_494_ = v___y_558_;
v___y_495_ = v___y_560_;
v___y_496_ = v___y_559_;
v___y_497_ = v___y_561_;
v___y_498_ = v___y_562_;
v___y_499_ = v___y_564_;
v___y_500_ = v___y_565_;
v___y_501_ = v___x_567_;
goto v___jp_492_;
}
v___jp_571_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_586_ = lean_string_push(v___x_585_, v___y_580_);
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
v___x_597_ = lean_string_append(v___x_596_, v___y_574_);
v___x_598_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = lean_string_append(v___x_599_, v___y_572_);
lean_dec_ref(v___y_572_);
v___x_601_ = lean_string_append(v___x_600_, v___x_598_);
v___x_602_ = lean_string_append(v___x_601_, v_caption_569_);
lean_dec_ref(v_caption_569_);
v___x_603_ = lean_string_append(v___x_602_, v___y_584_);
lean_dec_ref(v___y_584_);
if (v_useAnsi_467_ == 0)
{
v___y_493_ = v___y_578_;
v___y_494_ = v___y_579_;
v___y_495_ = v___y_582_;
v___y_496_ = v___y_581_;
v___y_497_ = v___y_573_;
v___y_498_ = v___y_575_;
v___y_499_ = v___y_576_;
v___y_500_ = v___y_577_;
v___y_501_ = v___x_603_;
goto v___jp_492_;
}
else
{
if (v___y_582_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_557_ = v___y_578_;
v___y_558_ = v___y_579_;
v___y_559_ = v___y_581_;
v___y_560_ = v___y_582_;
v___y_561_ = v___y_573_;
v___y_562_ = v___y_575_;
v___y_563_ = v___x_603_;
v___y_564_ = v___y_576_;
v___y_565_ = v___y_577_;
v___y_566_ = v___x_604_;
goto v___jp_556_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = l_Lake_LogLevel_ansiColor(v___y_583_);
v___y_557_ = v___y_578_;
v___y_558_ = v___y_579_;
v___y_559_ = v___y_581_;
v___y_560_ = v___y_582_;
v___y_561_ = v___y_573_;
v___y_562_ = v___y_575_;
v___y_563_ = v___x_603_;
v___y_564_ = v___y_576_;
v___y_565_ = v___y_577_;
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
lean_dec(v___y_625_);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_633_;
v___y_610_ = v___y_623_;
v___y_611_ = v___y_624_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_627_;
v___y_614_ = v___y_628_;
v___y_615_ = v___y_629_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
goto v___jp_606_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v___y_627_, v___y_625_);
if (v___x_634_ == 0)
{
lean_dec(v___y_625_);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_633_;
v___y_610_ = v___y_623_;
v___y_611_ = v___y_624_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_627_;
v___y_614_ = v___y_628_;
v___y_615_ = v___y_629_;
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
goto v___jp_606_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_636_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_625_);
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___y_572_ = v___y_621_;
v___y_573_ = v___y_622_;
v___y_574_ = v___y_633_;
v___y_575_ = v___y_623_;
v___y_576_ = v___y_624_;
v___y_577_ = v___y_626_;
v___y_578_ = v___y_627_;
v___y_579_ = v___y_628_;
v___y_580_ = v___y_629_;
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
v___y_621_ = v___y_646_;
v___y_622_ = v___y_645_;
v___y_623_ = v___y_647_;
v___y_624_ = v___y_649_;
v___y_625_ = v___y_650_;
v___y_626_ = v___y_651_;
v___y_627_ = v___y_641_;
v___y_628_ = v___y_642_;
v___y_629_ = v___y_652_;
v___y_630_ = v___y_644_;
v___y_631_ = v___y_643_;
v___y_632_ = v___y_648_;
v___y_633_ = v___x_653_;
goto v___jp_620_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_621_ = v___y_646_;
v___y_622_ = v___y_645_;
v___y_623_ = v___y_647_;
v___y_624_ = v___y_649_;
v___y_625_ = v___y_650_;
v___y_626_ = v___y_651_;
v___y_627_ = v___y_641_;
v___y_628_ = v___y_642_;
v___y_629_ = v___y_652_;
v___y_630_ = v___y_644_;
v___y_631_ = v___y_643_;
v___y_632_ = v___y_648_;
v___y_633_ = v___x_654_;
goto v___jp_620_;
}
}
v___jp_655_:
{
if (v___y_659_ == 0)
{
if (v_showProgress_468_ == 0)
{
lean_dec(v___y_665_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_658_;
goto v___jp_439_;
}
else
{
if (v_useAnsi_467_ == 0)
{
if (v___y_661_ == 0)
{
lean_dec(v___y_665_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_658_;
goto v___jp_439_;
}
else
{
lean_object* v___x_667_; uint32_t v___x_668_; 
v___x_667_ = l_Lake_JobAction_verb(v___y_664_, v___y_662_);
v___x_668_ = 10004;
v___y_641_ = v___y_656_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_659_;
v___y_644_ = v___y_658_;
v___y_645_ = v___y_660_;
v___y_646_ = v___x_667_;
v___y_647_ = v___y_661_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_666_;
v___y_652_ = v___x_668_;
goto v___jp_640_;
}
}
else
{
lean_dec(v___y_665_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_658_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v___x_669_; uint32_t v___x_670_; 
v___x_669_ = l_Lake_JobAction_verb(v___y_664_, v___y_662_);
v___x_670_ = l_Lake_LogLevel_icon(v___y_663_);
v___y_641_ = v___y_656_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_659_;
v___y_644_ = v___y_658_;
v___y_645_ = v___y_660_;
v___y_646_ = v___x_669_;
v___y_647_ = v___y_659_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_666_;
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
v___y_659_ = v___y_682_;
v___y_660_ = v___y_675_;
v___y_661_ = v___y_676_;
v___y_662_ = v___y_677_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_679_;
v___y_665_ = v___y_680_;
v___y_666_ = v___y_681_;
goto v___jp_655_;
}
else
{
if (v_showOptional_466_ == 0)
{
lean_dec(v___y_680_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_674_;
goto v___jp_439_;
}
else
{
v___y_656_ = v___y_672_;
v___y_657_ = v___y_673_;
v___y_658_ = v___y_674_;
v___y_659_ = v___y_682_;
v___y_660_ = v___y_675_;
v___y_661_ = v___y_676_;
v___y_662_ = v___y_677_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_679_;
v___y_665_ = v___y_680_;
v___y_666_ = v___y_681_;
goto v___jp_655_;
}
}
}
v___jp_683_:
{
if (v___y_691_ == 0)
{
if (v___y_688_ == 0)
{
v___y_672_ = v___y_684_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_695_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_693_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_688_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___y_684_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_695_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_693_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_692_;
goto v___jp_671_;
}
}
else
{
if (v_optional_570_ == 0)
{
lean_object* v_jobNo_696_; lean_object* v_totalJobs_697_; uint8_t v_wantsRebuild_698_; lean_object* v_failures_699_; lean_object* v_resetCtrl_700_; lean_object* v_lastUpdate_701_; lean_object* v_spinnerIdx_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_jobNo_696_ = lean_ctor_get(v___y_695_, 0);
v_totalJobs_697_ = lean_ctor_get(v___y_695_, 1);
v_wantsRebuild_698_ = lean_ctor_get_uint8(v___y_695_, sizeof(void*)*6);
v_failures_699_ = lean_ctor_get(v___y_695_, 2);
v_resetCtrl_700_ = lean_ctor_get(v___y_695_, 3);
v_lastUpdate_701_ = lean_ctor_get(v___y_695_, 4);
v_spinnerIdx_702_ = lean_ctor_get(v___y_695_, 5);
v_isSharedCheck_710_ = !lean_is_exclusive(v___y_695_);
if (v_isSharedCheck_710_ == 0)
{
v___x_704_ = v___y_695_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_spinnerIdx_702_);
lean_inc(v_lastUpdate_701_);
lean_inc(v_resetCtrl_700_);
lean_inc(v_failures_699_);
lean_inc(v_totalJobs_697_);
lean_inc(v_jobNo_696_);
lean_dec(v___y_695_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_inc_ref(v_caption_569_);
v___x_706_ = lean_array_push(v_failures_699_, v_caption_569_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 2, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_jobNo_696_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_totalJobs_697_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_resetCtrl_700_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_lastUpdate_701_);
lean_ctor_set(v_reuseFailAlloc_709_, 5, v_spinnerIdx_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_709_, sizeof(void*)*6, v_wantsRebuild_698_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v___y_672_ = v___y_684_;
v___y_673_ = v___y_685_;
v___y_674_ = v___x_708_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_693_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_691_;
goto v___jp_671_;
}
}
}
else
{
v___y_672_ = v___y_684_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_695_;
v___y_675_ = v___y_686_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_693_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_691_;
goto v___jp_671_;
}
}
}
v___jp_711_:
{
if (v___y_713_ == 0)
{
v___y_684_ = v___y_712_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_722_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_720_;
v___y_693_ = v___y_721_;
v___y_694_ = v_a_436_;
v___y_695_ = v_a_437_;
goto v___jp_683_;
}
else
{
if (v_wantsRebuild_457_ == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_inc(v_spinnerIdx_461_);
lean_inc(v_lastUpdate_460_);
lean_inc_ref(v_resetCtrl_459_);
lean_inc_ref(v_failures_458_);
v_isSharedCheck_729_ = !lean_is_exclusive(v_a_437_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; 
v_unused_730_ = lean_ctor_get(v_a_437_, 5);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_a_437_, 4);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_a_437_, 3);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_a_437_, 2);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_a_437_, 1);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_a_437_, 0);
lean_dec(v_unused_735_);
v___x_724_ = v_a_437_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_a_437_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
lean_inc(v_totalJobs_456_);
lean_inc(v_jobNo_455_);
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_jobNo_455_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_totalJobs_456_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_failures_458_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_resetCtrl_459_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_lastUpdate_460_);
lean_ctor_set(v_reuseFailAlloc_728_, 5, v_spinnerIdx_461_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*6, v___y_713_);
v___y_684_ = v___y_712_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_722_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_720_;
v___y_693_ = v___y_721_;
v___y_694_ = v_a_436_;
v___y_695_ = v___x_727_;
goto v___jp_683_;
}
}
}
else
{
v___y_684_ = v___y_712_;
v___y_685_ = v___y_714_;
v___y_686_ = v___y_715_;
v___y_687_ = v___y_722_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_720_;
v___y_693_ = v___y_721_;
v___y_694_ = v_a_436_;
v___y_695_ = v_a_437_;
goto v___jp_683_;
}
}
}
v___jp_736_:
{
uint8_t v___x_747_; 
v___x_747_ = l_Lake_instOrdJobAction_ord(v_minAction_465_, v___y_742_);
if (v___x_747_ == 2)
{
uint8_t v___x_748_; 
v___x_748_ = 0;
v___y_712_ = v___y_737_;
v___y_713_ = v___y_739_;
v___y_714_ = v___y_738_;
v___y_715_ = v___y_740_;
v___y_716_ = v___y_741_;
v___y_717_ = v___y_742_;
v___y_718_ = v___y_743_;
v___y_719_ = v___y_744_;
v___y_720_ = v___y_746_;
v___y_721_ = v___y_745_;
v___y_722_ = v___x_748_;
goto v___jp_711_;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 1;
v___y_712_ = v___y_737_;
v___y_713_ = v___y_739_;
v___y_714_ = v___y_738_;
v___y_715_ = v___y_740_;
v___y_716_ = v___y_741_;
v___y_717_ = v___y_742_;
v___y_718_ = v___y_743_;
v___y_719_ = v___y_744_;
v___y_720_ = v___y_746_;
v___y_721_ = v___y_745_;
v___y_722_ = v___x_749_;
goto v___jp_711_;
}
}
v___jp_750_:
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_strict_and(v___y_755_, v___y_759_);
v___x_761_ = l_Lake_instOrdLogLevel_ord(v_outLv_463_, v___y_757_);
if (v___x_761_ == 2)
{
uint8_t v___x_762_; 
v___x_762_ = 0;
v___y_737_ = v___y_751_;
v___y_738_ = v___y_753_;
v___y_739_ = v___y_752_;
v___y_740_ = v___y_754_;
v___y_741_ = v___y_755_;
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___x_760_;
v___y_745_ = v___y_758_;
v___y_746_ = v___x_762_;
goto v___jp_736_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 1;
v___y_737_ = v___y_751_;
v___y_738_ = v___y_753_;
v___y_739_ = v___y_752_;
v___y_740_ = v___y_754_;
v___y_741_ = v___y_755_;
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___x_760_;
v___y_745_ = v___y_758_;
v___y_746_ = v___x_763_;
goto v___jp_736_;
}
}
v___jp_764_:
{
uint8_t v___x_773_; 
v___x_773_ = l_Lake_instOrdLogLevel_ord(v_failLv_464_, v___y_770_);
if (v___x_773_ == 2)
{
uint8_t v___x_774_; 
v___x_774_ = 0;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_767_;
v___y_753_ = v___y_766_;
v___y_754_ = v___y_768_;
v___y_755_ = v___y_772_;
v___y_756_ = v___y_769_;
v___y_757_ = v___y_770_;
v___y_758_ = v___y_771_;
v___y_759_ = v___x_774_;
goto v___jp_750_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = 1;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_767_;
v___y_753_ = v___y_766_;
v___y_754_ = v___y_768_;
v___y_755_ = v___y_772_;
v___y_756_ = v___y_769_;
v___y_757_ = v___y_770_;
v___y_758_ = v___y_771_;
v___y_759_ = v___x_775_;
goto v___jp_750_;
}
}
v___jp_776_:
{
lean_object* v_log_778_; uint8_t v_action_779_; uint8_t v_wantsRebuild_780_; lean_object* v_buildTime_781_; uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_log_778_ = lean_ctor_get(v___y_777_, 0);
lean_inc_ref(v_log_778_);
v_action_779_ = lean_ctor_get_uint8(v___y_777_, sizeof(void*)*3);
v_wantsRebuild_780_ = lean_ctor_get_uint8(v___y_777_, sizeof(void*)*3 + 1);
v_buildTime_781_ = lean_ctor_get(v___y_777_, 2);
lean_inc(v_buildTime_781_);
lean_dec_ref(v___y_777_);
v___x_782_ = l_Lake_Log_maxLv(v_log_778_);
v___x_783_ = lean_array_get_size(v_log_778_);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_nat_dec_eq(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
uint8_t v___x_786_; 
v___x_786_ = 1;
v___y_765_ = v___x_784_;
v___y_766_ = v___x_783_;
v___y_767_ = v_wantsRebuild_780_;
v___y_768_ = v_log_778_;
v___y_769_ = v_action_779_;
v___y_770_ = v___x_782_;
v___y_771_ = v_buildTime_781_;
v___y_772_ = v___x_786_;
goto v___jp_764_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = 0;
v___y_765_ = v___x_784_;
v___y_766_ = v___x_783_;
v___y_767_ = v_wantsRebuild_780_;
v___y_768_ = v_log_778_;
v___y_769_ = v_action_779_;
v___y_770_ = v___x_782_;
v___y_771_ = v_buildTime_781_;
v___y_772_ = v___x_787_;
goto v___jp_764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_790_, v_a_791_, v_a_792_);
lean_dec_ref(v_a_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_795_, uint8_t v___y_796_, uint8_t v_useAnsi_797_, lean_object* v_as_798_, size_t v_i_799_, size_t v_stop_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_795_, v___y_796_, v_useAnsi_797_, v_as_798_, v_i_799_, v_stop_800_, v_b_801_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_806_, lean_object* v___y_807_, lean_object* v_useAnsi_808_, lean_object* v_as_809_, lean_object* v_i_810_, lean_object* v_stop_811_, lean_object* v_b_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v___y_14553__boxed_816_; uint8_t v_useAnsi_14554__boxed_817_; size_t v_i_boxed_818_; size_t v_stop_boxed_819_; lean_object* v_res_820_; 
v___y_14553__boxed_816_ = lean_unbox(v___y_807_);
v_useAnsi_14554__boxed_817_ = lean_unbox(v_useAnsi_808_);
v_i_boxed_818_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_stop_boxed_819_ = lean_unbox_usize(v_stop_811_);
lean_dec(v_stop_811_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_806_, v___y_14553__boxed_816_, v_useAnsi_14554__boxed_817_, v_as_809_, v_i_boxed_818_, v_stop_boxed_819_, v_b_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_as_809_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_jobs_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_jobNo_830_; lean_object* v_totalJobs_831_; uint8_t v_wantsRebuild_832_; lean_object* v_failures_833_; lean_object* v_resetCtrl_834_; lean_object* v_lastUpdate_835_; lean_object* v_spinnerIdx_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_846_; 
v_jobs_826_ = lean_ctor_get(v_a_823_, 0);
v___x_827_ = lean_st_ref_take(v_jobs_826_);
v___x_828_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_829_ = lean_st_ref_put(v_jobs_826_, v___x_828_);
v_jobNo_830_ = lean_ctor_get(v_a_824_, 0);
v_totalJobs_831_ = lean_ctor_get(v_a_824_, 1);
v_wantsRebuild_832_ = lean_ctor_get_uint8(v_a_824_, sizeof(void*)*6);
v_failures_833_ = lean_ctor_get(v_a_824_, 2);
v_resetCtrl_834_ = lean_ctor_get(v_a_824_, 3);
v_lastUpdate_835_ = lean_ctor_get(v_a_824_, 4);
v_spinnerIdx_836_ = lean_ctor_get(v_a_824_, 5);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_846_ == 0)
{
v___x_838_ = v_a_824_;
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_spinnerIdx_836_);
lean_inc(v_lastUpdate_835_);
lean_inc(v_resetCtrl_834_);
lean_inc(v_failures_833_);
lean_inc(v_totalJobs_831_);
lean_inc(v_jobNo_830_);
lean_dec(v_a_824_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_array_get_size(v___x_827_);
v___x_841_ = lean_nat_add(v_totalJobs_831_, v___x_840_);
lean_dec(v_totalJobs_831_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_jobNo_830_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_failures_833_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_resetCtrl_834_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_lastUpdate_835_);
lean_ctor_set(v_reuseFailAlloc_845_, 5, v_spinnerIdx_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_845_, sizeof(void*)*6, v_wantsRebuild_832_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_827_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_847_, v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(lean_object* v_as_851_, size_t v_i_852_, size_t v_stop_853_, lean_object* v_b_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_fst_859_; lean_object* v_snd_860_; uint8_t v___x_864_; 
v___x_864_ = lean_usize_dec_eq(v_i_852_, v_stop_853_);
if (v___x_864_ == 0)
{
lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_867_; lean_object* v_task_868_; uint8_t v___x_869_; 
v_fst_865_ = lean_ctor_get(v_b_854_, 0);
v_snd_866_ = lean_ctor_get(v_b_854_, 1);
v___x_867_ = lean_array_uget_borrowed(v_as_851_, v_i_852_);
v_task_868_ = lean_ctor_get(v___x_867_, 0);
v___x_869_ = lean_io_get_task_state(v_task_868_);
switch(v___x_869_)
{
case 0:
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
lean_inc(v_snd_866_);
lean_inc(v_fst_865_);
v_isSharedCheck_877_ = !lean_is_exclusive(v_b_854_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_878_ = lean_ctor_get(v_b_854_, 1);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_b_854_, 0);
lean_dec(v_unused_879_);
v___x_871_ = v_b_854_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_b_854_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v___x_867_);
v___x_873_ = lean_array_push(v_snd_866_, v___x_867_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_fst_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_fst_859_ = v___x_875_;
v_snd_860_ = v___y_856_;
goto v___jp_858_;
}
}
}
case 1:
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_888_; 
lean_inc(v_snd_866_);
lean_inc(v_fst_865_);
v_isSharedCheck_888_ = !lean_is_exclusive(v_b_854_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; 
v_unused_889_ = lean_ctor_get(v_b_854_, 1);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_b_854_, 0);
lean_dec(v_unused_890_);
v___x_881_ = v_b_854_;
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
else
{
lean_dec(v_b_854_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_888_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_inc_n(v___x_867_, 2);
v___x_883_ = lean_array_push(v_fst_865_, v___x_867_);
v___x_884_ = lean_array_push(v_snd_866_, v___x_867_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_884_);
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v_fst_859_ = v___x_886_;
v_snd_860_ = v___y_856_;
goto v___jp_858_;
}
}
}
default: 
{
lean_object* v___x_891_; lean_object* v_snd_892_; lean_object* v_jobNo_893_; lean_object* v_totalJobs_894_; uint8_t v_wantsRebuild_895_; lean_object* v_failures_896_; lean_object* v_resetCtrl_897_; lean_object* v_lastUpdate_898_; lean_object* v_spinnerIdx_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_908_; 
lean_inc(v___x_867_);
v___x_891_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v___x_867_, v___y_855_, v___y_856_);
v_snd_892_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_snd_892_);
lean_dec_ref(v___x_891_);
v_jobNo_893_ = lean_ctor_get(v_snd_892_, 0);
v_totalJobs_894_ = lean_ctor_get(v_snd_892_, 1);
v_wantsRebuild_895_ = lean_ctor_get_uint8(v_snd_892_, sizeof(void*)*6);
v_failures_896_ = lean_ctor_get(v_snd_892_, 2);
v_resetCtrl_897_ = lean_ctor_get(v_snd_892_, 3);
v_lastUpdate_898_ = lean_ctor_get(v_snd_892_, 4);
v_spinnerIdx_899_ = lean_ctor_get(v_snd_892_, 5);
v_isSharedCheck_908_ = !lean_is_exclusive(v_snd_892_);
if (v_isSharedCheck_908_ == 0)
{
v___x_901_ = v_snd_892_;
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_spinnerIdx_899_);
lean_inc(v_lastUpdate_898_);
lean_inc(v_resetCtrl_897_);
lean_inc(v_failures_896_);
lean_inc(v_totalJobs_894_);
lean_inc(v_jobNo_893_);
lean_dec(v_snd_892_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_908_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_jobNo_893_, v___x_903_);
lean_dec(v_jobNo_893_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_904_);
v___x_906_ = v___x_901_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_totalJobs_894_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_failures_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_resetCtrl_897_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_lastUpdate_898_);
lean_ctor_set(v_reuseFailAlloc_907_, 5, v_spinnerIdx_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*6, v_wantsRebuild_895_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v_fst_859_ = v_b_854_;
v_snd_860_ = v___x_906_;
goto v___jp_858_;
}
}
}
}
}
else
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_b_854_);
lean_ctor_set(v___x_909_, 1, v___y_856_);
return v___x_909_;
}
v___jp_858_:
{
size_t v___x_861_; size_t v___x_862_; 
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_852_, v___x_861_);
v_i_852_ = v___x_862_;
v_b_854_ = v_fst_859_;
v___y_856_ = v_snd_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(lean_object* v_as_910_, lean_object* v_i_911_, lean_object* v_stop_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_i_boxed_917_; size_t v_stop_boxed_918_; lean_object* v_res_919_; 
v_i_boxed_917_ = lean_unbox_usize(v_i_911_);
lean_dec(v_i_911_);
v_stop_boxed_918_ = lean_unbox_usize(v_stop_912_);
lean_dec(v_stop_912_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_910_, v_i_boxed_917_, v_stop_boxed_918_, v_b_913_, v___y_914_, v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_as_910_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(lean_object* v_new_922_, lean_object* v_unfinished_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___y_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___y_942_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_945_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0));
v___x_946_ = lean_array_get_size(v_unfinished_923_);
v___x_947_ = lean_nat_dec_lt(v___x_927_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_inc_ref(v_a_925_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_945_);
lean_ctor_set(v___x_948_, 1, v_a_925_);
v___y_929_ = v___x_948_;
v_fst_930_ = v___x_945_;
v_snd_931_ = v_a_925_;
goto v___jp_928_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = lean_nat_dec_le(v___x_946_, v___x_946_);
if (v___x_949_ == 0)
{
if (v___x_947_ == 0)
{
lean_object* v___x_950_; 
lean_inc_ref(v_a_925_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_945_);
lean_ctor_set(v___x_950_, 1, v_a_925_);
v___y_929_ = v___x_950_;
v_fst_930_ = v___x_945_;
v_snd_931_ = v_a_925_;
goto v___jp_928_;
}
else
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_946_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_923_, v___x_951_, v___x_952_, v___x_945_, v_a_924_, v_a_925_);
v___y_942_ = v___x_953_;
goto v___jp_941_;
}
}
else
{
size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
v___x_954_ = ((size_t)0ULL);
v___x_955_ = lean_usize_of_nat(v___x_946_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_923_, v___x_954_, v___x_955_, v___x_945_, v_a_924_, v_a_925_);
v___y_942_ = v___x_956_;
goto v___jp_941_;
}
}
v___jp_928_:
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_array_get_size(v_new_922_);
v___x_933_ = lean_nat_dec_lt(v___x_927_, v___x_932_);
if (v___x_933_ == 0)
{
lean_dec_ref(v_snd_931_);
lean_dec_ref(v_fst_930_);
return v___y_929_;
}
else
{
uint8_t v___x_934_; 
v___x_934_ = lean_nat_dec_le(v___x_932_, v___x_932_);
if (v___x_934_ == 0)
{
if (v___x_933_ == 0)
{
lean_dec_ref(v_snd_931_);
lean_dec_ref(v_fst_930_);
return v___y_929_;
}
else
{
size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; 
lean_dec_ref(v___y_929_);
v___x_935_ = ((size_t)0ULL);
v___x_936_ = lean_usize_of_nat(v___x_932_);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_922_, v___x_935_, v___x_936_, v_fst_930_, v_a_924_, v_snd_931_);
return v___x_937_;
}
}
else
{
size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v___y_929_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = lean_usize_of_nat(v___x_932_);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_922_, v___x_938_, v___x_939_, v_fst_930_, v_a_924_, v_snd_931_);
return v___x_940_;
}
}
}
v___jp_941_:
{
lean_object* v_fst_943_; lean_object* v_snd_944_; 
v_fst_943_ = lean_ctor_get(v___y_942_, 0);
lean_inc(v_fst_943_);
v_snd_944_ = lean_ctor_get(v___y_942_, 1);
lean_inc(v_snd_944_);
v___y_929_ = v___y_942_;
v_fst_930_ = v_fst_943_;
v_snd_931_ = v_snd_944_;
goto v___jp_928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(lean_object* v_new_957_, lean_object* v_unfinished_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_957_, v_unfinished_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v_unfinished_958_);
lean_dec_ref(v_new_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___y_967_; lean_object* v___x_985_; lean_object* v_lastUpdate_986_; lean_object* v_updateFrequency_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_985_ = lean_io_mono_ms_now();
v_lastUpdate_986_ = lean_ctor_get(v_a_964_, 4);
v_updateFrequency_987_ = lean_ctor_get(v_a_963_, 2);
v___x_988_ = lean_nat_sub(v___x_985_, v_lastUpdate_986_);
lean_dec(v___x_985_);
v___x_989_ = lean_nat_sub(v_updateFrequency_987_, v___x_988_);
lean_dec(v___x_988_);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_nat_dec_lt(v___x_990_, v___x_989_);
if (v___x_991_ == 0)
{
lean_dec(v___x_989_);
v___y_967_ = v_a_964_;
goto v___jp_966_;
}
else
{
uint32_t v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_uint32_of_nat(v___x_989_);
lean_dec(v___x_989_);
v___x_993_ = l_IO_sleep(v___x_992_);
v___y_967_ = v_a_964_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v_jobNo_969_; lean_object* v_totalJobs_970_; uint8_t v_wantsRebuild_971_; lean_object* v_failures_972_; lean_object* v_resetCtrl_973_; lean_object* v_spinnerIdx_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_983_; 
v___x_968_ = lean_io_mono_ms_now();
v_jobNo_969_ = lean_ctor_get(v___y_967_, 0);
v_totalJobs_970_ = lean_ctor_get(v___y_967_, 1);
v_wantsRebuild_971_ = lean_ctor_get_uint8(v___y_967_, sizeof(void*)*6);
v_failures_972_ = lean_ctor_get(v___y_967_, 2);
v_resetCtrl_973_ = lean_ctor_get(v___y_967_, 3);
v_spinnerIdx_974_ = lean_ctor_get(v___y_967_, 5);
v_isSharedCheck_983_ = !lean_is_exclusive(v___y_967_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___y_967_, 4);
lean_dec(v_unused_984_);
v___x_976_ = v___y_967_;
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_spinnerIdx_974_);
lean_inc(v_resetCtrl_973_);
lean_inc(v_failures_972_);
lean_inc(v_totalJobs_970_);
lean_inc(v_jobNo_969_);
lean_dec(v___y_967_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 4, v___x_968_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_jobNo_969_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_totalJobs_970_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_failures_972_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_resetCtrl_973_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_982_, 5, v_spinnerIdx_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_982_, sizeof(void*)*6, v_wantsRebuild_971_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_994_, v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* v_new_998_, lean_object* v_unfinished_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___y_1009_; lean_object* v___y_1010_; uint8_t v_failFast_1036_; 
v___x_1003_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(v_new_998_, v_unfinished_999_, v_a_1000_, v_a_1001_);
lean_dec_ref(v_unfinished_999_);
lean_dec_ref(v_new_998_);
v_fst_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_fst_1004_);
v_snd_1005_ = lean_ctor_get(v___x_1003_, 1);
lean_inc(v_snd_1005_);
lean_dec_ref(v___x_1003_);
v_fst_1006_ = lean_ctor_get(v_fst_1004_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v_fst_1004_, 1);
lean_inc(v_snd_1007_);
lean_dec(v_fst_1004_);
v_failFast_1036_ = lean_ctor_get_uint8(v_a_1000_, sizeof(void*)*4 + 7);
if (v_failFast_1036_ == 0)
{
v___y_1009_ = v_a_1000_;
v___y_1010_ = v_snd_1005_;
goto v___jp_1008_;
}
else
{
lean_object* v_cancelTk_x3f_1037_; 
v_cancelTk_x3f_1037_ = lean_ctor_get(v_a_1000_, 3);
if (lean_obj_tag(v_cancelTk_x3f_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v_failures_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_val_1038_ = lean_ctor_get(v_cancelTk_x3f_1037_, 0);
v_failures_1039_ = lean_ctor_get(v_snd_1005_, 2);
v___x_1040_ = lean_array_get_size(v_failures_1039_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_nat_dec_eq(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
v___x_1043_ = l_IO_CancelToken_set(v_val_1038_);
v___y_1009_ = v_a_1000_;
v___y_1010_ = v_snd_1005_;
goto v___jp_1008_;
}
else
{
v___y_1009_ = v_a_1000_;
v___y_1010_ = v_snd_1005_;
goto v___jp_1008_;
}
}
else
{
v___y_1009_ = v_a_1000_;
v___y_1010_ = v_snd_1005_;
goto v___jp_1008_;
}
}
v___jp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_array_get_size(v_snd_1007_);
v___x_1013_ = lean_nat_dec_lt(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_fst_1006_);
v___x_1014_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1009_, v___y_1010_);
v_fst_1015_ = lean_ctor_get(v___x_1014_, 0);
v_snd_1016_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1018_ = v___x_1014_;
v_isShared_1019_ = v_isSharedCheck_1027_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snd_1016_);
lean_inc(v_fst_1015_);
lean_dec(v___x_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1027_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_array_get_size(v_fst_1015_);
v___x_1021_ = lean_nat_dec_lt(v___x_1011_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec(v_fst_1015_);
lean_dec(v_snd_1007_);
v___x_1022_ = lean_box(0);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_1016_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_del_object(v___x_1018_);
v_new_998_ = v_fst_1015_;
v_unfinished_999_ = v_snd_1007_;
v_a_1000_ = v___y_1009_;
v_a_1001_ = v_snd_1016_;
goto _start;
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v_snd_1029_; lean_object* v___x_1030_; lean_object* v_snd_1031_; lean_object* v___x_1032_; lean_object* v_fst_1033_; lean_object* v_snd_1034_; 
v___x_1028_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1006_, v_snd_1007_, v___y_1009_, v___y_1010_);
lean_dec(v_fst_1006_);
v_snd_1029_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_snd_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v___y_1009_, v_snd_1029_);
v_snd_1031_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_snd_1031_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v___y_1009_, v_snd_1031_);
v_fst_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_fst_1033_);
v_snd_1034_ = lean_ctor_get(v___x_1032_, 1);
lean_inc(v_snd_1034_);
lean_dec_ref(v___x_1032_);
v_new_998_ = v_fst_1033_;
v_unfinished_999_ = v_snd_1007_;
v_a_1000_ = v___y_1009_;
v_a_1001_ = v_snd_1034_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1044_, lean_object* v_unfinished_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1044_, v_unfinished_1045_, v_a_1046_, v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1125_; 
v___x_1054_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1051_, v_a_1052_);
v_fst_1055_ = lean_ctor_get(v___x_1054_, 0);
v_snd_1056_ = lean_ctor_get(v___x_1054_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1058_ = v___x_1054_;
v_isShared_1059_ = v_isSharedCheck_1125_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_snd_1056_);
lean_inc(v_fst_1055_);
lean_dec(v___x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1125_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v_snd_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1123_; 
v___x_1060_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1055_, v_init_1050_, v_a_1051_, v_snd_1056_);
v_snd_1061_ = lean_ctor_get(v___x_1060_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___x_1060_, 0);
lean_dec(v_unused_1124_);
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1123_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snd_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1123_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_jobNo_1065_; lean_object* v_totalJobs_1066_; uint8_t v_wantsRebuild_1067_; lean_object* v_failures_1068_; lean_object* v_resetCtrl_1069_; lean_object* v_lastUpdate_1070_; lean_object* v_spinnerIdx_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1122_; 
v_jobNo_1065_ = lean_ctor_get(v_snd_1061_, 0);
v_totalJobs_1066_ = lean_ctor_get(v_snd_1061_, 1);
v_wantsRebuild_1067_ = lean_ctor_get_uint8(v_snd_1061_, sizeof(void*)*6);
v_failures_1068_ = lean_ctor_get(v_snd_1061_, 2);
v_resetCtrl_1069_ = lean_ctor_get(v_snd_1061_, 3);
v_lastUpdate_1070_ = lean_ctor_get(v_snd_1061_, 4);
v_spinnerIdx_1071_ = lean_ctor_get(v_snd_1061_, 5);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_snd_1061_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1073_ = v_snd_1061_;
v_isShared_1074_ = v_isSharedCheck_1122_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_spinnerIdx_1071_);
lean_inc(v_lastUpdate_1070_);
lean_inc(v_resetCtrl_1069_);
lean_inc(v_failures_1068_);
lean_inc(v_totalJobs_1066_);
lean_inc(v_jobNo_1065_);
lean_dec(v_snd_1061_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1122_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 3, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_jobNo_1065_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_totalJobs_1066_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_failures_1068_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_lastUpdate_1070_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_spinnerIdx_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6, v_wantsRebuild_1067_);
v___x_1077_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v_val_1079_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = lean_string_utf8_byte_size(v_resetCtrl_1069_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_nat_dec_eq(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v_out_1086_; lean_object* v_flush_1087_; lean_object* v_putStr_1088_; lean_object* v___x_1093_; 
lean_del_object(v___x_1058_);
v_out_1086_ = lean_ctor_get(v_a_1051_, 1);
v_flush_1087_ = lean_ctor_get(v_out_1086_, 0);
v_putStr_1088_ = lean_ctor_get(v_out_1086_, 4);
lean_inc_ref(v_putStr_1088_);
lean_inc_ref(v_resetCtrl_1069_);
v___x_1093_ = lean_apply_2(v_putStr_1088_, v_resetCtrl_1069_, lean_box(0));
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_dec_ref_known(v___x_1093_, 1);
lean_dec_ref(v_resetCtrl_1069_);
goto v___jp_1089_;
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1116_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1116_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1116_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1098_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1099_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1100_ = lean_unsigned_to_nat(82u);
v___x_1101_ = lean_unsigned_to_nat(4u);
v___x_1102_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1103_ = lean_io_error_to_string(v_a_1094_);
v___x_1104_ = lean_string_append(v___x_1102_, v___x_1103_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1106_ = lean_string_append(v___x_1104_, v___x_1105_);
v___x_1107_ = l_String_quote(v_resetCtrl_1069_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 3);
lean_ctor_set(v___x_1096_, 0, v___x_1107_);
v___x_1109_ = v___x_1096_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1110_ = l_Std_Format_defWidth;
v___x_1111_ = l_Std_Format_pretty(v___x_1109_, v___x_1110_, v___x_1084_, v___x_1084_);
v___x_1112_ = lean_string_append(v___x_1106_, v___x_1111_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = l_mkPanicMessageWithDecl(v___x_1098_, v___x_1099_, v___x_1100_, v___x_1101_, v___x_1112_);
lean_dec_ref(v___x_1112_);
v___x_1114_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1113_);
goto v___jp_1089_;
}
}
}
v___jp_1089_:
{
lean_object* v___x_1090_; 
lean_inc_ref(v_flush_1087_);
v___x_1090_ = lean_apply_1(v_flush_1087_, lean_box(0));
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v_val_1079_ = v_a_1091_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1092_; 
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_box(0);
v_val_1079_ = v___x_1092_;
goto v___jp_1078_;
}
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
lean_dec_ref(v_resetCtrl_1069_);
lean_del_object(v___x_1063_);
v___x_1117_ = lean_box(0);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1077_);
lean_ctor_set(v___x_1058_, 0, v___x_1117_);
v___x_1119_ = v___x_1058_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1077_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
v___jp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1077_);
lean_ctor_set(v___x_1063_, 0, v_val_1079_);
v___x_1081_ = v___x_1063_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_val_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1077_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1126_, v_a_1127_, v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1131_){
_start:
{
lean_object* v_failures_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_failures_1132_ = lean_ctor_get(v_self_1131_, 0);
v___x_1133_ = lean_array_get_size(v_failures_1132_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_nat_dec_eq(v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1136_);
lean_dec_ref(v_self_1136_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0(void){
_start:
{
uint8_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = 2;
v___x_1140_ = l_Lake_Verbosity_ctorIdx(v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1141_, lean_object* v_jobs_1142_, lean_object* v_cancelTk_x3f_1143_){
_start:
{
lean_object* v_toLogConfig_1145_; uint8_t v_failFast_1146_; uint8_t v_verbosity_1147_; uint8_t v_failLv_1148_; uint8_t v_outLv_1149_; uint8_t v_ansiMode_1150_; lean_object* v_out_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; uint8_t v___y_1159_; uint8_t v___y_1160_; uint8_t v___y_1164_; 
v_toLogConfig_1145_ = lean_ctor_get(v_cfg_1141_, 0);
v_failFast_1146_ = lean_ctor_get_uint8(v_cfg_1141_, sizeof(void*)*4 + 3);
v_verbosity_1147_ = lean_ctor_get_uint8(v_cfg_1141_, sizeof(void*)*4 + 4);
v_failLv_1148_ = lean_ctor_get_uint8(v_toLogConfig_1145_, sizeof(void*)*1);
v_outLv_1149_ = lean_ctor_get_uint8(v_toLogConfig_1145_, sizeof(void*)*1 + 1);
v_ansiMode_1150_ = lean_ctor_get_uint8(v_toLogConfig_1145_, sizeof(void*)*1 + 2);
v_out_1151_ = lean_ctor_get(v_toLogConfig_1145_, 0);
v___x_1152_ = l_Lake_OutStream_get(v_out_1151_);
lean_inc_ref(v___x_1152_);
v___x_1153_ = l_Lake_AnsiMode_isEnabled(v___x_1152_, v_ansiMode_1150_);
v___x_1154_ = l_Lake_BuildConfig_showProgress(v_cfg_1141_);
v___x_1155_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1147_);
v___x_1156_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0, &l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0);
v___x_1157_ = lean_nat_dec_eq(v___x_1155_, v___x_1156_);
lean_dec(v___x_1155_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1166_; 
v___x_1166_ = 3;
v___y_1164_ = v___x_1166_;
goto v___jp_1163_;
}
else
{
uint8_t v___x_1167_; 
v___x_1167_ = 0;
v___y_1164_ = v___x_1167_;
goto v___jp_1163_;
}
v___jp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(100u);
v___x_1162_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_1162_, 0, v_jobs_1142_);
lean_ctor_set(v___x_1162_, 1, v___x_1152_);
lean_ctor_set(v___x_1162_, 2, v___x_1161_);
lean_ctor_set(v___x_1162_, 3, v_cancelTk_x3f_1143_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4, v_outLv_1149_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 1, v_failLv_1148_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 2, v___y_1159_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 3, v___x_1157_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 4, v___x_1153_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 5, v___x_1154_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 6, v___y_1160_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*4 + 7, v_failFast_1146_);
return v___x_1162_;
}
v___jp_1163_:
{
if (v___x_1157_ == 0)
{
if (v___x_1153_ == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
v___y_1159_ = v___y_1164_;
v___y_1160_ = v___x_1165_;
goto v___jp_1158_;
}
else
{
v___y_1159_ = v___y_1164_;
v___y_1160_ = v___x_1157_;
goto v___jp_1158_;
}
}
else
{
v___y_1159_ = v___y_1164_;
v___y_1160_ = v___x_1157_;
goto v___jp_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1168_, lean_object* v_jobs_1169_, lean_object* v_cancelTk_x3f_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1168_, v_jobs_1169_, v_cancelTk_x3f_1170_);
lean_dec_ref(v_cfg_1168_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1173_, lean_object* v_initJobs_1174_, lean_object* v_initFailures_1175_, lean_object* v_resetCtrl_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_snd_1183_; lean_object* v_totalJobs_1184_; uint8_t v_wantsRebuild_1185_; lean_object* v_failures_1186_; lean_object* v___x_1187_; 
v___x_1178_ = lean_io_mono_ms_now();
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = 0;
v___x_1181_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
lean_ctor_set(v___x_1181_, 2, v_initFailures_1175_);
lean_ctor_set(v___x_1181_, 3, v_resetCtrl_1176_);
lean_ctor_set(v___x_1181_, 4, v___x_1178_);
lean_ctor_set(v___x_1181_, 5, v___x_1179_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*6, v___x_1180_);
v___x_1182_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1174_, v_ctx_1173_, v___x_1181_);
v_snd_1183_ = lean_ctor_get(v___x_1182_, 1);
lean_inc(v_snd_1183_);
lean_dec_ref(v___x_1182_);
v_totalJobs_1184_ = lean_ctor_get(v_snd_1183_, 1);
lean_inc(v_totalJobs_1184_);
v_wantsRebuild_1185_ = lean_ctor_get_uint8(v_snd_1183_, sizeof(void*)*6);
v_failures_1186_ = lean_ctor_get(v_snd_1183_, 2);
lean_inc_ref(v_failures_1186_);
lean_dec(v_snd_1183_);
v___x_1187_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1187_, 0, v_failures_1186_);
lean_ctor_set(v___x_1187_, 1, v_totalJobs_1184_);
lean_ctor_set_uint8(v___x_1187_, sizeof(void*)*2, v_wantsRebuild_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1188_, lean_object* v_initJobs_1189_, lean_object* v_initFailures_1190_, lean_object* v_resetCtrl_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1188_, v_initJobs_1189_, v_initFailures_1190_, v_resetCtrl_1191_);
lean_dec_ref(v_ctx_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1194_, lean_object* v_jobs_1195_, lean_object* v_out_1196_, uint8_t v_failLv_1197_, uint8_t v_outLv_1198_, uint8_t v_minAction_1199_, uint8_t v_showOptional_1200_, uint8_t v_useAnsi_1201_, uint8_t v_showProgress_1202_, uint8_t v_showTime_1203_, lean_object* v_resetCtrl_1204_, lean_object* v_initFailures_1205_, lean_object* v_updateFrequency_1206_){
_start:
{
uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v_ctx_1210_; lean_object* v___x_1211_; 
v___x_1208_ = 0;
v___x_1209_ = lean_box(0);
v_ctx_1210_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_ctx_1210_, 0, v_jobs_1195_);
lean_ctor_set(v_ctx_1210_, 1, v_out_1196_);
lean_ctor_set(v_ctx_1210_, 2, v_updateFrequency_1206_);
lean_ctor_set(v_ctx_1210_, 3, v___x_1209_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4, v_outLv_1198_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 1, v_failLv_1197_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 2, v_minAction_1199_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 3, v_showOptional_1200_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 4, v_useAnsi_1201_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 5, v_showProgress_1202_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 6, v_showTime_1203_);
lean_ctor_set_uint8(v_ctx_1210_, sizeof(void*)*4 + 7, v___x_1208_);
v___x_1211_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1210_, v_initJobs_1194_, v_initFailures_1205_, v_resetCtrl_1204_);
lean_dec_ref_known(v_ctx_1210_, 4);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1212_, lean_object* v_jobs_1213_, lean_object* v_out_1214_, lean_object* v_failLv_1215_, lean_object* v_outLv_1216_, lean_object* v_minAction_1217_, lean_object* v_showOptional_1218_, lean_object* v_useAnsi_1219_, lean_object* v_showProgress_1220_, lean_object* v_showTime_1221_, lean_object* v_resetCtrl_1222_, lean_object* v_initFailures_1223_, lean_object* v_updateFrequency_1224_, lean_object* v_a_1225_){
_start:
{
uint8_t v_failLv_boxed_1226_; uint8_t v_outLv_boxed_1227_; uint8_t v_minAction_boxed_1228_; uint8_t v_showOptional_boxed_1229_; uint8_t v_useAnsi_boxed_1230_; uint8_t v_showProgress_boxed_1231_; uint8_t v_showTime_boxed_1232_; lean_object* v_res_1233_; 
v_failLv_boxed_1226_ = lean_unbox(v_failLv_1215_);
v_outLv_boxed_1227_ = lean_unbox(v_outLv_1216_);
v_minAction_boxed_1228_ = lean_unbox(v_minAction_1217_);
v_showOptional_boxed_1229_ = lean_unbox(v_showOptional_1218_);
v_useAnsi_boxed_1230_ = lean_unbox(v_useAnsi_1219_);
v_showProgress_boxed_1231_ = lean_unbox(v_showProgress_1220_);
v_showTime_boxed_1232_ = lean_unbox(v_showTime_1221_);
v_res_1233_ = l_Lake_monitorJobs(v_initJobs_1212_, v_jobs_1213_, v_out_1214_, v_failLv_boxed_1226_, v_outLv_boxed_1227_, v_minAction_boxed_1228_, v_showOptional_boxed_1229_, v_useAnsi_boxed_1230_, v_showProgress_boxed_1231_, v_showTime_boxed_1232_, v_resetCtrl_1222_, v_initFailures_1223_, v_updateFrequency_1224_);
return v_res_1233_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1234_; 
v___x_1234_ = 3;
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_apply_2(v_logger_1235_, v___y_1237_, lean_box(0));
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1240_, lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1240_, v_x_1241_, v___y_1242_);
return v_res_1244_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1255_ = l_String_quote(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5);
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = l_Std_Format_defWidth;
v___x_1260_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1261_ = l_Std_Format_pretty(v___x_1260_, v___x_1259_, v___x_1258_, v___x_1258_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_1264_ = l_String_quote(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_1266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = l_Std_Format_defWidth;
v___x_1269_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1270_ = l_Std_Format_pretty(v___x_1269_, v___x_1268_, v___x_1267_, v___x_1267_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_1273_ = l_String_quote(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_1275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = l_Std_Format_defWidth;
v___x_1278_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_1279_ = l_Std_Format_pretty(v___x_1278_, v___x_1277_, v___x_1276_, v___x_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1281_, lean_object* v_ws_1282_, lean_object* v_outputsRef_x3f_1283_, lean_object* v_out_1284_, lean_object* v_outputsFile_1285_, uint8_t v_isVerbose_1286_){
_start:
{
lean_object* v___f_1290_; lean_object* v___x_1291_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1303_; lean_object* v___y_1304_; uint8_t v___x_1394_; 
lean_inc_ref(v_logger_1281_);
v___f_1290_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1290_, 0, v_logger_1281_);
v___x_1291_ = l_instMonadBaseIO;
v___x_1394_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1282_);
if (v___x_1394_ == 0)
{
lean_object* v_packages_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_baseName_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_packages_1395_ = lean_ctor_get(v_ws_1282_, 4);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_array_fget_borrowed(v_packages_1395_, v___x_1396_);
v_baseName_1398_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_baseName_1398_);
v___x_1399_ = l_Lean_Name_toString(v_baseName_1398_, v___x_1394_);
v___x_1400_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16));
v___x_1401_ = lean_string_append(v___x_1399_, v___x_1400_);
v___x_1402_ = 2;
v___x_1403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*1, v___x_1402_);
v___x_1404_ = lean_apply_2(v_logger_1281_, v___x_1403_, lean_box(0));
goto v___jp_1313_;
}
else
{
lean_dec_ref(v_logger_1281_);
goto v___jp_1313_;
}
v___jp_1288_:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_box(0);
return v___x_1289_;
}
v___jp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_array_get_size(v___y_1294_);
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_nat_dec_lt(v___y_1293_, v___x_1295_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v___y_1294_);
lean_dec_ref(v___f_1290_);
return v___x_1296_;
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1374__overap_1300_; lean_object* v___x_1301_; 
v___x_1298_ = ((size_t)0ULL);
v___x_1299_ = lean_usize_of_nat(v___x_1295_);
v___x_1374__overap_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1291_, v___f_1290_, v___y_1294_, v___x_1298_, v___x_1299_, v___x_1296_);
v___x_1301_ = lean_apply_1(v___x_1374__overap_1300_, lean_box(0));
return v___x_1301_;
}
}
v___jp_1302_:
{
if (v_isVerbose_1286_ == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref(v___y_1304_);
lean_dec_ref(v___f_1290_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_array_get_size(v___y_1304_);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_nat_dec_lt(v___y_1303_, v___x_1306_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v___y_1304_);
lean_dec_ref(v___f_1290_);
return v___x_1307_;
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1305__overap_1311_; lean_object* v___x_1312_; 
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = lean_usize_of_nat(v___x_1306_);
v___x_1305__overap_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1291_, v___f_1290_, v___y_1304_, v___x_1309_, v___x_1310_, v___x_1307_);
v___x_1312_ = lean_apply_1(v___x_1305__overap_1311_, lean_box(0));
return v___x_1312_;
}
}
}
v___jp_1313_:
{
if (lean_obj_tag(v_outputsRef_x3f_1283_) == 1)
{
lean_object* v_val_1314_; lean_object* v___x_1315_; lean_object* v_packages_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v_config_1319_; lean_object* v_toLeanConfig_1320_; lean_object* v_platformIndependent_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_val_1314_ = lean_ctor_get(v_outputsRef_x3f_1283_, 0);
v___x_1315_ = lean_st_ref_get(v_val_1314_);
v_packages_1316_ = lean_ctor_get(v_ws_1282_, 4);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_fget_borrowed(v_packages_1316_, v___x_1317_);
v_config_1319_ = lean_ctor_get(v___x_1318_, 6);
v_toLeanConfig_1320_ = lean_ctor_get(v_config_1319_, 1);
v_platformIndependent_1321_ = lean_ctor_get(v_toLeanConfig_1320_, 10);
v___f_1322_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1323_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
lean_inc(v_platformIndependent_1321_);
v___x_1324_ = l_Option_instBEq_beq___redArg(v___f_1322_, v_platformIndependent_1321_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1326_ = l_Lake_CacheMap_writeFile(v_outputsFile_1285_, v___x_1315_, v___x_1324_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 2);
v___x_1328_ = lean_array_get_size(v_a_1327_);
v___x_1329_ = lean_nat_dec_eq(v___x_1328_, v___x_1317_);
if (v___x_1329_ == 0)
{
if (v_isVerbose_1286_ == 0)
{
lean_dec(v_a_1327_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_out_1284_);
goto v___jp_1288_;
}
else
{
lean_object* v_putStr_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_putStr_1330_ = lean_ctor_get(v_out_1284_, 4);
lean_inc_ref(v_putStr_1330_);
lean_dec_ref(v_out_1284_);
v___x_1331_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1332_ = lean_apply_2(v_putStr_1330_, v___x_1331_, lean_box(0));
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_dec_ref_known(v___x_1332_, 1);
v___y_1293_ = v___x_1317_;
v___y_1294_ = v_a_1327_;
goto v___jp_1292_;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1569__overap_1352_; lean_object* v___x_1353_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1334_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1335_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1336_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1337_ = lean_unsigned_to_nat(82u);
v___x_1338_ = lean_unsigned_to_nat(4u);
v___x_1339_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1340_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1341_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1340_, v_isVerbose_1286_);
v___x_1342_ = lean_string_append(v___x_1339_, v___x_1341_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1344_ = lean_string_append(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_io_error_to_string(v_a_1333_);
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
v___x_1349_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
v___x_1351_ = l_mkPanicMessageWithDecl(v___x_1335_, v___x_1336_, v___x_1337_, v___x_1338_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1569__overap_1352_ = l_panic___redArg(v___x_1334_, v___x_1351_);
v___x_1353_ = lean_apply_1(v___x_1569__overap_1352_, lean_box(0));
v___y_1293_ = v___x_1317_;
v___y_1294_ = v_a_1327_;
goto v___jp_1292_;
}
}
}
else
{
lean_dec(v_a_1327_);
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_out_1284_);
goto v___jp_1288_;
}
}
else
{
lean_object* v_a_1354_; lean_object* v_putStr_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_a_1354_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1326_, 2);
v_putStr_1355_ = lean_ctor_get(v_out_1284_, 4);
lean_inc_ref(v_putStr_1355_);
lean_dec_ref(v_out_1284_);
v___x_1356_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_1357_ = lean_apply_2(v_putStr_1355_, v___x_1356_, lean_box(0));
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v___y_1303_ = v___x_1317_;
v___y_1304_ = v_a_1354_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1354__overap_1372_; lean_object* v___x_1373_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1360_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1361_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1362_ = lean_unsigned_to_nat(82u);
v___x_1363_ = lean_unsigned_to_nat(4u);
v___x_1364_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1365_ = lean_io_error_to_string(v_a_1358_);
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
v___x_1369_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
v___x_1371_ = l_mkPanicMessageWithDecl(v___x_1360_, v___x_1361_, v___x_1362_, v___x_1363_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1354__overap_1372_ = l_panic___redArg(v___x_1359_, v___x_1371_);
v___x_1373_ = lean_apply_1(v___x_1354__overap_1372_, lean_box(0));
v___y_1303_ = v___x_1317_;
v___y_1304_ = v_a_1354_;
goto v___jp_1302_;
}
}
}
else
{
lean_object* v_putStr_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v___f_1290_);
lean_dec_ref(v_outputsFile_1285_);
v_putStr_1374_ = lean_ctor_get(v_out_1284_, 4);
lean_inc_ref(v_putStr_1374_);
lean_dec_ref(v_out_1284_);
v___x_1375_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_1376_ = lean_apply_2(v_putStr_1374_, v___x_1375_, lean_box(0));
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
return v_a_1377_;
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1472__overap_1392_; lean_object* v___x_1393_; 
v_a_1378_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1379_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1380_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1381_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1382_ = lean_unsigned_to_nat(82u);
v___x_1383_ = lean_unsigned_to_nat(4u);
v___x_1384_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1385_ = lean_io_error_to_string(v_a_1378_);
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
v___x_1389_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15);
v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
v___x_1391_ = l_mkPanicMessageWithDecl(v___x_1380_, v___x_1381_, v___x_1382_, v___x_1383_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1472__overap_1392_ = l_panic___redArg(v___x_1379_, v___x_1391_);
v___x_1393_ = lean_apply_1(v___x_1472__overap_1392_, lean_box(0));
return v___x_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1405_, lean_object* v_ws_1406_, lean_object* v_outputsRef_x3f_1407_, lean_object* v_out_1408_, lean_object* v_outputsFile_1409_, lean_object* v_isVerbose_1410_, lean_object* v_a_1411_){
_start:
{
uint8_t v_isVerbose_boxed_1412_; lean_object* v_res_1413_; 
v_isVerbose_boxed_1412_ = lean_unbox(v_isVerbose_1410_);
v_res_1413_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1405_, v_ws_1406_, v_outputsRef_x3f_1407_, v_out_1408_, v_outputsFile_1409_, v_isVerbose_boxed_1412_);
lean_dec(v_outputsRef_x3f_1407_);
lean_dec_ref(v_ws_1406_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1415_, lean_object* v_as_1416_, size_t v_i_1417_, size_t v_stop_1418_, lean_object* v_b_1419_){
_start:
{
lean_object* v_val_1422_; uint8_t v___x_1426_; 
v___x_1426_ = lean_usize_dec_eq(v_i_1417_, v_stop_1418_);
if (v___x_1426_ == 0)
{
lean_object* v_putStr_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_putStr_1427_ = lean_ctor_get(v_out_1415_, 4);
v___x_1428_ = lean_array_uget_borrowed(v_as_1416_, v_i_1417_);
v___x_1429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1430_ = lean_string_append(v___x_1429_, v___x_1428_);
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1432_ = lean_string_append(v___x_1430_, v___x_1431_);
lean_inc_ref(v_putStr_1427_);
lean_inc_ref(v___x_1432_);
v___x_1433_ = lean_apply_2(v_putStr_1427_, v___x_1432_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; 
lean_dec_ref(v___x_1432_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v_val_1422_ = v_a_1434_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1458_; 
v_a_1435_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1437_ = v___x_1433_;
v_isShared_1438_ = v_isSharedCheck_1458_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1458_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1439_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1440_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1441_ = lean_unsigned_to_nat(82u);
v___x_1442_ = lean_unsigned_to_nat(4u);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1445_ = lean_io_error_to_string(v_a_1435_);
v___x_1446_ = lean_string_append(v___x_1444_, v___x_1445_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1448_ = lean_string_append(v___x_1446_, v___x_1447_);
v___x_1449_ = l_String_quote(v___x_1432_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 3);
lean_ctor_set(v___x_1437_, 0, v___x_1449_);
v___x_1451_ = v___x_1437_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1452_ = l_Std_Format_defWidth;
v___x_1453_ = l_Std_Format_pretty(v___x_1451_, v___x_1452_, v___x_1443_, v___x_1443_);
v___x_1454_ = lean_string_append(v___x_1448_, v___x_1453_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = l_mkPanicMessageWithDecl(v___x_1439_, v___x_1440_, v___x_1441_, v___x_1442_, v___x_1454_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1455_);
v_val_1422_ = v___x_1456_;
goto v___jp_1421_;
}
}
}
}
else
{
lean_dec_ref(v_out_1415_);
return v_b_1419_;
}
v___jp_1421_:
{
size_t v___x_1423_; size_t v___x_1424_; 
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_add(v_i_1417_, v___x_1423_);
v_i_1417_ = v___x_1424_;
v_b_1419_ = v_val_1422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1459_, lean_object* v_as_1460_, lean_object* v_i_1461_, lean_object* v_stop_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_){
_start:
{
size_t v_i_boxed_1465_; size_t v_stop_boxed_1466_; lean_object* v_res_1467_; 
v_i_boxed_1465_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_stop_boxed_1466_ = lean_unbox_usize(v_stop_1462_);
lean_dec(v_stop_1462_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1459_, v_as_1460_, v_i_boxed_1465_, v_stop_boxed_1466_, v_b_1463_);
lean_dec_ref(v_as_1460_);
return v_res_1467_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1475_ = l_String_quote(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = l_Std_Format_defWidth;
v___x_1480_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1481_ = l_Std_Format_pretty(v___x_1480_, v___x_1479_, v___x_1478_, v___x_1478_);
return v___x_1481_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1484_ = l_String_quote(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = l_Std_Format_defWidth;
v___x_1489_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1490_ = l_Std_Format_pretty(v___x_1489_, v___x_1488_, v___x_1487_, v___x_1487_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1491_, lean_object* v_out_1492_, lean_object* v_result_1493_){
_start:
{
uint8_t v___y_1496_; lean_object* v___y_1497_; lean_object* v_failures_1571_; lean_object* v_numJobs_1572_; uint8_t v___y_1574_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_failures_1571_ = lean_ctor_get(v_result_1493_, 0);
lean_inc_ref(v_failures_1571_);
v_numJobs_1572_ = lean_ctor_get(v_result_1493_, 1);
lean_inc(v_numJobs_1572_);
lean_dec_ref(v_result_1493_);
v___x_1607_ = lean_array_get_size(v_failures_1571_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_nat_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v_flush_1610_; lean_object* v_putStr_1611_; lean_object* v___y_1617_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_numJobs_1572_);
v_flush_1610_ = lean_ctor_get(v_out_1492_, 0);
lean_inc_ref(v_flush_1610_);
v_putStr_1611_ = lean_ctor_get(v_out_1492_, 4);
v___x_1628_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1611_);
v___x_1629_ = lean_apply_2(v_putStr_1611_, v___x_1628_, lean_box(0));
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_dec_ref_known(v___x_1629_, 1);
goto v___jp_1618_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1632_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1633_ = lean_unsigned_to_nat(82u);
v___x_1634_ = lean_unsigned_to_nat(4u);
v___x_1635_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1636_ = lean_io_error_to_string(v_a_1630_);
v___x_1637_ = lean_string_append(v___x_1635_, v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1639_ = lean_string_append(v___x_1637_, v___x_1638_);
v___x_1640_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
v___x_1642_ = l_mkPanicMessageWithDecl(v___x_1631_, v___x_1632_, v___x_1633_, v___x_1634_, v___x_1641_);
lean_dec_ref(v___x_1641_);
v___x_1643_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1642_);
goto v___jp_1618_;
}
v___jp_1612_:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_apply_1(v_flush_1610_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
return v_a_1614_;
}
else
{
lean_object* v___x_1615_; 
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = lean_box(0);
return v___x_1615_;
}
}
v___jp_1616_:
{
goto v___jp_1612_;
}
v___jp_1618_:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_nat_dec_lt(v___x_1608_, v___x_1607_);
if (v___x_1619_ == 0)
{
lean_dec_ref(v_failures_1571_);
lean_dec_ref(v_out_1492_);
goto v___jp_1612_;
}
else
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_nat_dec_le(v___x_1607_, v___x_1607_);
if (v___x_1621_ == 0)
{
if (v___x_1619_ == 0)
{
lean_dec_ref(v_failures_1571_);
lean_dec_ref(v_out_1492_);
goto v___jp_1612_;
}
else
{
size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = lean_usize_of_nat(v___x_1607_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1492_, v_failures_1571_, v___x_1622_, v___x_1623_, v___x_1620_);
lean_dec_ref(v_failures_1571_);
v___y_1617_ = v___x_1624_;
goto v___jp_1616_;
}
}
else
{
size_t v___x_1625_; size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = lean_usize_of_nat(v___x_1607_);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1492_, v_failures_1571_, v___x_1625_, v___x_1626_, v___x_1620_);
lean_dec_ref(v_failures_1571_);
v___y_1617_ = v___x_1627_;
goto v___jp_1616_;
}
}
}
}
else
{
uint8_t v___x_1644_; 
lean_dec_ref(v_failures_1571_);
v___x_1644_ = l_Lake_BuildConfig_showProgress(v_cfg_1491_);
if (v___x_1644_ == 0)
{
v___y_1574_ = v___x_1644_;
goto v___jp_1573_;
}
else
{
uint8_t v_showSuccess_1645_; 
v_showSuccess_1645_ = lean_ctor_get_uint8(v_cfg_1491_, sizeof(void*)*4 + 5);
v___y_1574_ = v_showSuccess_1645_;
goto v___jp_1573_;
}
}
v___jp_1495_:
{
uint8_t v_noBuild_1498_; 
v_noBuild_1498_ = lean_ctor_get_uint8(v_cfg_1491_, sizeof(void*)*4 + 2);
if (v_noBuild_1498_ == 0)
{
lean_object* v_putStr_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_putStr_1499_ = lean_ctor_get(v_out_1492_, 4);
lean_inc_ref(v_putStr_1499_);
lean_dec_ref(v_out_1492_);
v___x_1500_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1501_ = lean_string_append(v___x_1500_, v___y_1497_);
lean_dec_ref(v___y_1497_);
v___x_1502_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1503_ = lean_string_append(v___x_1501_, v___x_1502_);
lean_inc_ref(v___x_1503_);
v___x_1504_ = lean_apply_2(v_putStr_1499_, v___x_1503_, lean_box(0));
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; 
lean_dec_ref(v___x_1503_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
return v_a_1505_;
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1534_; 
v_a_1506_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1508_ = v___x_1504_;
v_isShared_1509_ = v_isSharedCheck_1534_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1534_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1510_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1511_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1512_ = lean_unsigned_to_nat(82u);
v___x_1513_ = lean_unsigned_to_nat(4u);
v___x_1514_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1517_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1516_, v___y_1496_);
v___x_1518_ = lean_string_append(v___x_1514_, v___x_1517_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_io_error_to_string(v_a_1506_);
v___x_1522_ = lean_string_append(v___x_1520_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1524_ = lean_string_append(v___x_1522_, v___x_1523_);
v___x_1525_ = l_String_quote(v___x_1503_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 3);
lean_ctor_set(v___x_1508_, 0, v___x_1525_);
v___x_1527_ = v___x_1508_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = l_Std_Format_defWidth;
v___x_1529_ = l_Std_Format_pretty(v___x_1527_, v___x_1528_, v___x_1515_, v___x_1515_);
v___x_1530_ = lean_string_append(v___x_1524_, v___x_1529_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = l_mkPanicMessageWithDecl(v___x_1510_, v___x_1511_, v___x_1512_, v___x_1513_, v___x_1530_);
lean_dec_ref(v___x_1530_);
v___x_1532_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1531_);
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_putStr_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_putStr_1535_ = lean_ctor_get(v_out_1492_, 4);
lean_inc_ref(v_putStr_1535_);
lean_dec_ref(v_out_1492_);
v___x_1536_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1537_ = lean_string_append(v___x_1536_, v___y_1497_);
lean_dec_ref(v___y_1497_);
v___x_1538_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1539_ = lean_string_append(v___x_1537_, v___x_1538_);
lean_inc_ref(v___x_1539_);
v___x_1540_ = lean_apply_2(v_putStr_1535_, v___x_1539_, lean_box(0));
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; 
lean_dec_ref(v___x_1539_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
return v_a_1541_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1570_; 
v_a_1542_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1544_ = v___x_1540_;
v_isShared_1545_ = v_isSharedCheck_1570_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1570_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1546_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1547_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1548_ = lean_unsigned_to_nat(82u);
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1550_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1553_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1552_, v_noBuild_1498_);
v___x_1554_ = lean_string_append(v___x_1550_, v___x_1553_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_io_error_to_string(v_a_1542_);
v___x_1558_ = lean_string_append(v___x_1556_, v___x_1557_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
v___x_1561_ = l_String_quote(v___x_1539_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set_tag(v___x_1544_, 3);
lean_ctor_set(v___x_1544_, 0, v___x_1561_);
v___x_1563_ = v___x_1544_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1564_ = l_Std_Format_defWidth;
v___x_1565_ = l_Std_Format_pretty(v___x_1563_, v___x_1564_, v___x_1551_, v___x_1551_);
v___x_1566_ = lean_string_append(v___x_1560_, v___x_1565_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = l_mkPanicMessageWithDecl(v___x_1546_, v___x_1547_, v___x_1548_, v___x_1549_, v___x_1566_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1567_);
return v___x_1568_;
}
}
}
}
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec(v_numJobs_1572_);
lean_dec_ref(v_out_1492_);
v___x_1575_ = lean_box(0);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = lean_nat_dec_eq(v_numJobs_1572_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_dec_eq(v_numJobs_1572_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = l_Nat_reprFast(v_numJobs_1572_);
v___x_1581_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1582_ = lean_string_append(v___x_1580_, v___x_1581_);
v___y_1496_ = v___y_1574_;
v___y_1497_ = v___x_1582_;
goto v___jp_1495_;
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_numJobs_1572_);
v___x_1583_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1496_ = v___y_1574_;
v___y_1497_ = v___x_1583_;
goto v___jp_1495_;
}
}
else
{
lean_object* v_putStr_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v_numJobs_1572_);
v_putStr_1584_ = lean_ctor_get(v_out_1492_, 4);
lean_inc_ref(v_putStr_1584_);
lean_dec_ref(v_out_1492_);
v___x_1585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1586_ = lean_apply_2(v_putStr_1584_, v___x_1585_, lean_box(0));
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
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_a_1588_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1589_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1590_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1591_ = lean_unsigned_to_nat(82u);
v___x_1592_ = lean_unsigned_to_nat(4u);
v___x_1593_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1594_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1595_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1594_, v___x_1577_);
v___x_1596_ = lean_string_append(v___x_1593_, v___x_1595_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1598_ = lean_string_append(v___x_1596_, v___x_1597_);
v___x_1599_ = lean_io_error_to_string(v_a_1588_);
v___x_1600_ = lean_string_append(v___x_1598_, v___x_1599_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1602_ = lean_string_append(v___x_1600_, v___x_1601_);
v___x_1603_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1604_ = lean_string_append(v___x_1602_, v___x_1603_);
v___x_1605_ = l_mkPanicMessageWithDecl(v___x_1589_, v___x_1590_, v___x_1591_, v___x_1592_, v___x_1604_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1605_);
return v___x_1606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1646_, lean_object* v_out_1647_, lean_object* v_result_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1646_, v_out_1647_, v_result_1648_);
lean_dec_ref(v_cfg_1646_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1651_){
_start:
{
lean_object* v_toMonitorResult_1652_; 
v_toMonitorResult_1652_ = lean_ctor_get(v_self_1651_, 0);
lean_inc_ref(v_toMonitorResult_1652_);
return v_toMonitorResult_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1653_);
lean_dec_ref(v_self_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1656_){
_start:
{
lean_object* v___f_1657_; 
v___f_1657_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1657_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1658_){
_start:
{
lean_object* v_out_1659_; 
v_out_1659_ = lean_ctor_get(v_self_1658_, 1);
if (lean_obj_tag(v_out_1659_) == 0)
{
uint8_t v___x_1660_; 
v___x_1660_ = 0;
return v___x_1660_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = 1;
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1662_){
_start:
{
uint8_t v_res_1663_; lean_object* v_r_1664_; 
v_res_1663_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1662_);
lean_dec_ref(v_self_1662_);
v_r_1664_ = lean_box(v_res_1663_);
return v_r_1664_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1665_, lean_object* v_self_1666_){
_start:
{
lean_object* v_out_1667_; 
v_out_1667_ = lean_ctor_get(v_self_1666_, 1);
if (lean_obj_tag(v_out_1667_) == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = 0;
return v___x_1668_;
}
else
{
uint8_t v___x_1669_; 
v___x_1669_ = 1;
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_self_1671_){
_start:
{
uint8_t v_res_1672_; lean_object* v_r_1673_; 
v_res_1672_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1670_, v_self_1671_);
lean_dec_ref(v_self_1671_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1682_, lean_object* v_job_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_failures_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
lean_inc_ref(v_job_1683_);
v___x_1685_ = l_Lake_Job_toOpaque___redArg(v_job_1683_);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
v___x_1688_ = lean_array_push(v___x_1687_, v___x_1685_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1691_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1692_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1682_, v___x_1688_, v___x_1690_, v___x_1691_);
v_failures_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc_ref(v_failures_1693_);
v___x_1694_ = lean_array_get_size(v_failures_1693_);
lean_dec_ref(v_failures_1693_);
v___x_1695_ = lean_nat_dec_eq(v___x_1694_, v___x_1689_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v_job_1683_);
v___x_1696_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1692_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
return v___x_1697_;
}
else
{
lean_object* v_task_1698_; lean_object* v___x_1699_; 
v_task_1698_ = lean_ctor_get(v_job_1683_, 0);
lean_inc_ref(v_task_1698_);
lean_dec_ref(v_job_1683_);
v___x_1699_ = lean_io_wait(v_task_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1699_, 1);
lean_dec(v_unused_1709_);
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_a_1700_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1704_);
lean_ctor_set(v___x_1702_, 0, v___x_1692_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; lean_object* v_unused_1719_; 
v_unused_1718_ = lean_ctor_get(v___x_1699_, 1);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v___x_1699_, 0);
lean_dec(v_unused_1719_);
v___x_1711_ = v___x_1699_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_dec(v___x_1699_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
lean_ctor_set(v___x_1711_, 0, v___x_1692_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1720_, lean_object* v_job_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1720_, v_job_1721_);
lean_dec_ref(v_ctx_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1724_, lean_object* v_ctx_1725_, lean_object* v_job_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1725_, v_job_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_ctx_1730_, lean_object* v_job_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1729_, v_ctx_1730_, v_job_1731_);
lean_dec_ref(v_ctx_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object* v_info_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lake_computeTextFileHash(v_info_1736_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = lean_io_metadata(v_info_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1752_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1752_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1752_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_modified_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint64_t v___x_1748_; lean_object* v___x_1750_; 
v_modified_1745_ = lean_ctor_get(v_a_1741_, 1);
lean_inc_ref(v_modified_1745_);
lean_dec(v_a_1741_);
v___x_1746_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1747_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1747_, 0, v_info_1736_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
lean_ctor_set(v___x_1747_, 2, v_modified_1745_);
v___x_1748_ = lean_unbox_uint64(v_a_1739_);
lean_dec(v_a_1739_);
lean_ctor_set_uint64(v___x_1747_, sizeof(void*)*3, v___x_1748_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1747_);
v___x_1750_ = v___x_1743_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1747_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_a_1739_);
lean_dec_ref(v_info_1736_);
v_a_1753_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1740_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1740_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v_info_1736_);
v_a_1761_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1738_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1738_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
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
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object* v_info_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object* v___x_1775_, lean_object* v_as_1776_, size_t v_sz_1777_, size_t v_i_1778_, lean_object* v_b_1779_){
_start:
{
lean_object* v_a_1782_; uint8_t v___x_1786_; 
v___x_1786_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v___x_1775_);
return v_b_1779_;
}
else
{
lean_object* v_snd_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1810_; 
v_snd_1787_ = lean_ctor_get(v_b_1779_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_b_1779_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v_b_1779_, 0);
lean_dec(v_unused_1811_);
v___x_1789_ = v_b_1779_;
v_isShared_1790_ = v_isSharedCheck_1810_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_snd_1787_);
lean_dec(v_b_1779_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1810_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1791_ = lean_box(0);
v_a_1792_ = lean_array_uget_borrowed(v_as_1776_, v_i_1778_);
v___x_1793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0));
lean_inc_ref(v___x_1775_);
v___x_1794_ = l_Lake_joinRelative(v___x_1775_, v___x_1793_);
lean_inc(v_a_1792_);
v___x_1795_ = l_Lake_joinRelative(v___x_1794_, v_a_1792_);
v___x_1796_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v___x_1795_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l_Lake_BuildTrace_mix(v_snd_1787_, v_a_1797_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1798_);
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1800_ = v___x_1789_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
v_a_1782_ = v___x_1800_;
goto v___jp_1781_;
}
}
else
{
lean_object* v_a_1802_; 
v_a_1802_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1796_, 1);
if (lean_obj_tag(v_a_1802_) == 11)
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v_a_1802_, 2);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1804_ = v___x_1789_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1787_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
v_a_1782_ = v___x_1804_;
goto v___jp_1781_;
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_dec(v_a_1802_);
lean_dec_ref(v___x_1775_);
v___x_1806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1));
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1806_);
v___x_1808_ = v___x_1789_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_snd_1787_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
v___jp_1781_:
{
size_t v___x_1783_; size_t v___x_1784_; 
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1778_, v___x_1783_);
v_i_1778_ = v___x_1784_;
v_b_1779_ = v_a_1782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object* v___x_1812_, lean_object* v_as_1813_, lean_object* v_sz_1814_, lean_object* v_i_1815_, lean_object* v_b_1816_, lean_object* v___y_1817_){
_start:
{
size_t v_sz_boxed_1818_; size_t v_i_boxed_1819_; lean_object* v_res_1820_; 
v_sz_boxed_1818_ = lean_unbox_usize(v_sz_1814_);
lean_dec(v_sz_1814_);
v_i_boxed_1819_ = lean_unbox_usize(v_i_1815_);
lean_dec(v_i_1815_);
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1812_, v_as_1813_, v_sz_boxed_1818_, v_i_boxed_1819_, v_b_1816_);
lean_dec_ref(v_as_1813_);
return v_res_1820_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1));
v___x_1824_ = l_Lake_BuildTrace_nil(v___x_1823_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1839_);
return v___x_1841_;
}
}
static size_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1842_; size_t v_sz_1843_; 
v___x_1842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v_sz_1843_ = lean_array_size(v___x_1842_);
return v_sz_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t v_sz_1844_, size_t v_i_1845_, lean_object* v_bs_1846_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_lt(v_i_1845_, v_sz_1844_);
if (v___x_1848_ == 0)
{
return v_bs_1846_;
}
else
{
lean_object* v_v_1849_; lean_object* v_config_1850_; lean_object* v_dir_1851_; uint8_t v_bootstrap_1852_; lean_object* v_buildDir_1853_; lean_object* v___x_1854_; lean_object* v_bs_x27_1855_; lean_object* v_val_1857_; 
v_v_1849_ = lean_array_uget_borrowed(v_bs_1846_, v_i_1845_);
v_config_1850_ = lean_ctor_get(v_v_1849_, 6);
v_dir_1851_ = lean_ctor_get(v_v_1849_, 4);
lean_inc_ref(v_dir_1851_);
v_bootstrap_1852_ = lean_ctor_get_uint8(v_config_1850_, sizeof(void*)*28);
v_buildDir_1853_ = lean_ctor_get(v_config_1850_, 5);
lean_inc_ref(v_buildDir_1853_);
v___x_1854_ = lean_unsigned_to_nat(0u);
v_bs_x27_1855_ = lean_array_uset(v_bs_1846_, v_i_1845_, v___x_1854_);
if (v_bootstrap_1852_ == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_buildDir_1853_);
lean_dec_ref(v_dir_1851_);
v___x_1862_ = lean_box(0);
v_val_1857_ = v___x_1862_;
goto v___jp_1856_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; size_t v_sz_1869_; size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v_fst_1872_; 
v___x_1863_ = l_System_FilePath_normalize(v_buildDir_1853_);
v___x_1864_ = l_Lake_joinRelative(v_dir_1851_, v___x_1863_);
v___x_1865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0));
v___x_1866_ = l_Lake_joinRelative(v___x_1864_, v___x_1865_);
v___x_1867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v___x_1868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8);
v_sz_1869_ = lean_usize_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9);
v___x_1870_ = ((size_t)0ULL);
lean_inc_ref(v___x_1866_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1866_, v___x_1867_, v_sz_1869_, v___x_1870_, v___x_1868_);
v_fst_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_fst_1872_);
if (lean_obj_tag(v_fst_1872_) == 0)
{
lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1881_; 
v_snd_1873_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1871_, 0);
lean_dec(v_unused_1882_);
v___x_1875_ = v___x_1871_;
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_dec(v___x_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1881_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1866_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_snd_1873_);
v___x_1878_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
v_val_1857_ = v___x_1879_;
goto v___jp_1856_;
}
}
}
else
{
lean_object* v_val_1883_; 
lean_dec_ref(v___x_1871_);
lean_dec_ref(v___x_1866_);
v_val_1883_ = lean_ctor_get(v_fst_1872_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v_fst_1872_, 1);
v_val_1857_ = v_val_1883_;
goto v___jp_1856_;
}
}
v___jp_1856_:
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = lean_usize_add(v_i_1845_, v___x_1858_);
v___x_1860_ = lean_array_uset(v_bs_x27_1855_, v_i_1845_, v_val_1857_);
v_i_1845_ = v___x_1859_;
v_bs_1846_ = v___x_1860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object* v_sz_1884_, lean_object* v_i_1885_, lean_object* v_bs_1886_, lean_object* v___y_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1884_);
lean_dec(v_sz_1884_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_boxed_1888_, v_i_boxed_1889_, v_bs_1886_);
return v_res_1890_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = l_Lean_versionStringCore;
v___x_1893_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0));
v___x_1894_ = lean_string_append(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2));
v___x_1897_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1);
v___x_1898_ = lean_string_append(v___x_1897_, v___x_1896_);
return v___x_1898_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_nat_to_int(v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5(void){
_start:
{
uint32_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = 0;
v___x_1902_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4);
v___x_1903_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set_uint32(v___x_1903_, sizeof(void*)*1, v___x_1901_);
return v___x_1903_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_unsigned_to_nat(16u);
v___x_1906_ = lean_mk_array(v___x_1905_, v___x_1904_);
return v___x_1906_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6);
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v___x_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object* v_ws_1912_, lean_object* v_cfg_1913_, lean_object* v_jobs_1914_, lean_object* v_cancelTk_x3f_1915_){
_start:
{
uint8_t v___y_1918_; uint8_t v___y_1919_; uint8_t v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1926_; uint8_t v___y_1927_; lean_object* v_val_1928_; lean_object* v_val_1946_; uint8_t v___x_1968_; 
v___x_1968_ = l_System_Platform_isOSX;
if (v___x_1968_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_1969_; 
v_macosxDeploymentTarget_x3f_1969_ = lean_ctor_get(v_cfg_1913_, 3);
lean_inc(v_macosxDeploymentTarget_x3f_1969_);
v_val_1946_ = v_macosxDeploymentTarget_x3f_1969_;
goto v___jp_1945_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_1970_; 
v_macosxDeploymentTarget_x3f_1970_ = lean_ctor_get(v_cfg_1913_, 3);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___y_1974_; 
v___x_1971_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8));
v___x_1972_ = lean_io_getenv(v___x_1971_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9));
v___y_1974_ = v___x_1976_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_1977_; 
v_val_1977_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_val_1977_);
lean_dec_ref_known(v___x_1972_, 1);
v___y_1974_ = v_val_1977_;
goto v___jp_1973_;
}
v___jp_1973_:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1974_);
v_val_1946_ = v___x_1975_;
goto v___jp_1945_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_1970_);
v_val_1946_ = v_macosxDeploymentTarget_x3f_1970_;
goto v___jp_1945_;
}
}
v___jp_1917_:
{
lean_object* v_lakeEnv_1929_; lean_object* v_packages_1930_; size_t v_sz_1931_; size_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; uint64_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_lakeEnv_1929_ = lean_ctor_get(v_ws_1912_, 0);
v_packages_1930_ = lean_ctor_get(v_ws_1912_, 4);
v_sz_1931_ = lean_array_size(v_packages_1930_);
v___x_1932_ = ((size_t)0ULL);
lean_inc_ref(v_packages_1930_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_1931_, v___x_1932_, v_packages_1930_);
v___x_1934_ = lean_alloc_ctor(0, 4, 6);
lean_ctor_set(v___x_1934_, 0, v___y_1921_);
lean_ctor_set(v___x_1934_, 1, v___y_1926_);
lean_ctor_set(v___x_1934_, 2, v___y_1922_);
lean_ctor_set(v___x_1934_, 3, v___y_1923_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*4, v___y_1919_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*4 + 1, v___y_1927_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*4 + 2, v___y_1918_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*4 + 3, v___y_1925_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*4 + 4, v___y_1920_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*4 + 5, v___y_1924_);
v___x_1935_ = l_Lake_Env_leanGithash(v_lakeEnv_1929_);
v___x_1936_ = l_Lake_Hash_nil;
v___x_1937_ = lean_string_hash(v___x_1935_);
v___x_1938_ = lean_uint64_mix_hash(v___x_1936_, v___x_1937_);
v___x_1939_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3);
v___x_1940_ = lean_string_append(v___x_1939_, v___x_1935_);
lean_dec_ref(v___x_1935_);
v___x_1941_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1942_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5);
v___x_1943_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1943_, 0, v___x_1940_);
lean_ctor_set(v___x_1943_, 1, v___x_1941_);
lean_ctor_set(v___x_1943_, 2, v___x_1942_);
lean_ctor_set_uint64(v___x_1943_, sizeof(void*)*3, v___x_1938_);
v___x_1944_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1934_);
lean_ctor_set(v___x_1944_, 1, v_ws_1912_);
lean_ctor_set(v___x_1944_, 2, v___x_1943_);
lean_ctor_set(v___x_1944_, 3, v___x_1933_);
lean_ctor_set(v___x_1944_, 4, v_jobs_1914_);
lean_ctor_set(v___x_1944_, 5, v_val_1928_);
lean_ctor_set(v___x_1944_, 6, v_cancelTk_x3f_1915_);
return v___x_1944_;
}
v___jp_1945_:
{
lean_object* v_outputsFile_x3f_1947_; 
v_outputsFile_x3f_1947_ = lean_ctor_get(v_cfg_1913_, 1);
lean_inc(v_outputsFile_x3f_1947_);
if (lean_obj_tag(v_outputsFile_x3f_1947_) == 0)
{
lean_object* v_toLogConfig_1948_; uint8_t v_oldMode_1949_; uint8_t v_trustHash_1950_; uint8_t v_noBuild_1951_; uint8_t v_failFast_1952_; uint8_t v_verbosity_1953_; uint8_t v_showSuccess_1954_; lean_object* v_leanOptOverrides_1955_; lean_object* v___x_1956_; 
v_toLogConfig_1948_ = lean_ctor_get(v_cfg_1913_, 0);
lean_inc_ref(v_toLogConfig_1948_);
v_oldMode_1949_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4);
v_trustHash_1950_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 1);
v_noBuild_1951_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 2);
v_failFast_1952_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 3);
v_verbosity_1953_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 4);
v_showSuccess_1954_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 5);
v_leanOptOverrides_1955_ = lean_ctor_get(v_cfg_1913_, 2);
lean_inc(v_leanOptOverrides_1955_);
lean_dec_ref(v_cfg_1913_);
v___x_1956_ = lean_box(0);
v___y_1918_ = v_noBuild_1951_;
v___y_1919_ = v_oldMode_1949_;
v___y_1920_ = v_verbosity_1953_;
v___y_1921_ = v_toLogConfig_1948_;
v___y_1922_ = v_leanOptOverrides_1955_;
v___y_1923_ = v_val_1946_;
v___y_1924_ = v_showSuccess_1954_;
v___y_1925_ = v_failFast_1952_;
v___y_1926_ = v_outputsFile_x3f_1947_;
v___y_1927_ = v_trustHash_1950_;
v_val_1928_ = v___x_1956_;
goto v___jp_1917_;
}
else
{
lean_object* v_toLogConfig_1957_; uint8_t v_oldMode_1958_; uint8_t v_trustHash_1959_; uint8_t v_noBuild_1960_; uint8_t v_failFast_1961_; uint8_t v_verbosity_1962_; uint8_t v_showSuccess_1963_; lean_object* v_leanOptOverrides_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_toLogConfig_1957_ = lean_ctor_get(v_cfg_1913_, 0);
lean_inc_ref(v_toLogConfig_1957_);
v_oldMode_1958_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4);
v_trustHash_1959_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 1);
v_noBuild_1960_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 2);
v_failFast_1961_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 3);
v_verbosity_1962_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 4);
v_showSuccess_1963_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*4 + 5);
v_leanOptOverrides_1964_ = lean_ctor_get(v_cfg_1913_, 2);
lean_inc(v_leanOptOverrides_1964_);
lean_dec_ref(v_cfg_1913_);
v___x_1965_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7);
v___x_1966_ = lean_st_mk_ref(v___x_1965_);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
v___y_1918_ = v_noBuild_1960_;
v___y_1919_ = v_oldMode_1958_;
v___y_1920_ = v_verbosity_1962_;
v___y_1921_ = v_toLogConfig_1957_;
v___y_1922_ = v_leanOptOverrides_1964_;
v___y_1923_ = v_val_1946_;
v___y_1924_ = v_showSuccess_1963_;
v___y_1925_ = v_failFast_1961_;
v___y_1926_ = v_outputsFile_x3f_1947_;
v___y_1927_ = v_trustHash_1959_;
v_val_1928_ = v___x_1967_;
goto v___jp_1917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object* v_ws_1978_, lean_object* v_cfg_1979_, lean_object* v_jobs_1980_, lean_object* v_cancelTk_x3f_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_1978_, v_cfg_1979_, v_jobs_1980_, v_cancelTk_x3f_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_log_1992_; uint8_t v_action_1993_; uint8_t v_wantsRebuild_1994_; lean_object* v_trace_1995_; lean_object* v_buildTime_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2025_; 
v_log_1992_ = lean_ctor_get(v___y_1990_, 0);
v_action_1993_ = lean_ctor_get_uint8(v___y_1990_, sizeof(void*)*3);
v_wantsRebuild_1994_ = lean_ctor_get_uint8(v___y_1990_, sizeof(void*)*3 + 1);
v_trace_1995_ = lean_ctor_get(v___y_1990_, 1);
v_buildTime_1996_ = lean_ctor_get(v___y_1990_, 2);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___y_1990_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1998_ = v___y_1990_;
v_isShared_1999_ = v_isSharedCheck_2025_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_buildTime_1996_);
lean_inc(v_trace_1995_);
lean_inc(v_log_1992_);
lean_dec(v___y_1990_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2025_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_apply_7(v_build_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v_log_1992_, lean_box(0));
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2012_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_a_2002_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2012_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2012_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_a_2002_);
v___x_2007_ = v___x_1998_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2002_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_trace_1995_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_buildTime_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2011_, sizeof(void*)*3, v_action_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2011_, sizeof(void*)*3 + 1, v_wantsRebuild_1994_);
v___x_2007_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2007_);
v___x_2009_ = v___x_2004_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2001_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2024_; 
v_a_2013_ = lean_ctor_get(v___x_2000_, 0);
v_a_2014_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2016_ = v___x_2000_;
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_inc(v_a_2013_);
lean_dec(v___x_2000_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_a_2014_);
v___x_2019_ = v___x_1998_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_trace_1995_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_buildTime_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3, v_action_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 1, v_wantsRebuild_1994_);
v___x_2019_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_2019_);
v___x_2021_ = v___x_2016_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_2036_, lean_object* v_build_2037_, lean_object* v_caption_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2040_ = lean_box(1);
v___x_2041_ = lean_st_mk_ref(v___x_2040_);
v___f_2042_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2042_, 0, v_build_2037_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_box(0);
v___x_2047_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_2048_ = l_Lake_Job_async___redArg(v___x_2043_, v___f_2042_, v___x_2044_, v_caption_2038_, v___x_2047_, v___x_2046_, v___x_2045_, v___x_2041_, v_bctx_2036_);
v___x_2049_ = lean_st_ref_get(v___x_2041_);
lean_dec(v___x_2041_);
lean_dec(v___x_2049_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_2050_, lean_object* v_build_2051_, lean_object* v_caption_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2050_, v_build_2051_, v_caption_2052_);
lean_dec_ref(v_bctx_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_2055_, lean_object* v_bctx_2056_, lean_object* v_build_2057_, lean_object* v_caption_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2056_, v_build_2057_, v_caption_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_bctx_2062_, lean_object* v_build_2063_, lean_object* v_caption_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_2061_, v_bctx_2062_, v_build_2063_, v_caption_2064_);
lean_dec_ref(v_bctx_2062_);
return v_res_2066_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
if (lean_obj_tag(v_x_2067_) == 0)
{
if (lean_obj_tag(v_x_2068_) == 0)
{
uint8_t v___x_2069_; 
v___x_2069_ = 1;
return v___x_2069_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = 0;
return v___x_2070_;
}
}
else
{
if (lean_obj_tag(v_x_2068_) == 0)
{
uint8_t v___x_2071_; 
v___x_2071_ = 0;
return v___x_2071_;
}
else
{
lean_object* v_val_2072_; uint8_t v___x_2073_; 
v_val_2072_ = lean_ctor_get(v_x_2068_, 0);
v___x_2073_ = lean_unbox(v_val_2072_);
if (v___x_2073_ == 0)
{
lean_object* v_val_2074_; uint8_t v___x_2075_; 
v_val_2074_ = lean_ctor_get(v_x_2067_, 0);
v___x_2075_ = lean_unbox(v_val_2074_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
v___x_2076_ = 1;
return v___x_2076_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_unbox(v_val_2072_);
return v___x_2077_;
}
}
else
{
lean_object* v_val_2078_; uint8_t v___x_2079_; 
v_val_2078_ = lean_ctor_get(v_x_2067_, 0);
v___x_2079_ = lean_unbox(v_val_2078_);
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
uint8_t v_res_2082_; lean_object* v_r_2083_; 
v_res_2082_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_2080_, v_x_2081_);
lean_dec(v_x_2081_);
lean_dec(v_x_2080_);
v_r_2083_ = lean_box(v_res_2082_);
return v_r_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_2084_, uint8_t v___x_2085_, uint8_t v___x_2086_, lean_object* v_as_2087_, size_t v_i_2088_, size_t v_stop_2089_, lean_object* v_b_2090_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_eq(v_i_2088_, v_stop_2089_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; 
v___x_2093_ = lean_array_uget_borrowed(v_as_2087_, v_i_2088_);
lean_inc_ref(v___x_2084_);
v___x_2094_ = l_Lake_logToStream(v___x_2093_, v___x_2084_, v___x_2085_, v___x_2086_);
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2088_, v___x_2095_);
v_i_2088_ = v___x_2096_;
v_b_2090_ = v___x_2094_;
goto _start;
}
else
{
lean_dec_ref(v___x_2084_);
return v_b_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v_as_2101_, lean_object* v_i_2102_, lean_object* v_stop_2103_, lean_object* v_b_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_1007__boxed_2106_; uint8_t v___x_1008__boxed_2107_; size_t v_i_boxed_2108_; size_t v_stop_boxed_2109_; lean_object* v_res_2110_; 
v___x_1007__boxed_2106_ = lean_unbox(v___x_2099_);
v___x_1008__boxed_2107_ = lean_unbox(v___x_2100_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2102_);
lean_dec(v_i_2102_);
v_stop_boxed_2109_ = lean_unbox_usize(v_stop_2103_);
lean_dec(v_stop_2103_);
v_res_2110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2098_, v___x_1007__boxed_2106_, v___x_1008__boxed_2107_, v_as_2101_, v_i_boxed_2108_, v_stop_boxed_2109_, v_b_2104_);
lean_dec_ref(v_as_2101_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_2111_, uint8_t v___x_2112_, uint8_t v___x_2113_, lean_object* v_ws_2114_, lean_object* v_outputsRef_x3f_2115_, lean_object* v_out_2116_, lean_object* v_outputsFile_2117_, uint8_t v_isVerbose_2118_){
_start:
{
lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___x_2215_; 
v___x_2215_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_2114_);
if (v___x_2215_ == 0)
{
lean_object* v_packages_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_baseName_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_packages_2216_ = lean_ctor_get(v_ws_2114_, 4);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_array_fget_borrowed(v_packages_2216_, v___x_2217_);
v_baseName_2219_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_baseName_2219_);
v___x_2220_ = l_Lean_Name_toString(v_baseName_2219_, v___x_2215_);
v___x_2221_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16));
v___x_2222_ = lean_string_append(v___x_2220_, v___x_2221_);
v___x_2223_ = 2;
v___x_2224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*1, v___x_2223_);
lean_inc_ref(v___x_2111_);
v___x_2225_ = l_Lake_logToStream(v___x_2224_, v___x_2111_, v___x_2112_, v___x_2113_);
lean_dec_ref_known(v___x_2224_, 1);
goto v___jp_2141_;
}
else
{
goto v___jp_2141_;
}
v___jp_2120_:
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_box(0);
return v___x_2121_;
}
v___jp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_array_get_size(v___y_2123_);
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_nat_dec_lt(v___y_2124_, v___x_2125_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v___y_2123_);
lean_dec_ref(v___x_2111_);
return v___x_2126_;
}
else
{
size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = lean_usize_of_nat(v___x_2125_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2111_, v___x_2112_, v___x_2113_, v___y_2123_, v___x_2128_, v___x_2129_, v___x_2126_);
lean_dec_ref(v___y_2123_);
return v___x_2130_;
}
}
v___jp_2131_:
{
if (v_isVerbose_2118_ == 0)
{
lean_object* v___x_2134_; 
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___x_2111_);
v___x_2134_ = lean_box(0);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2135_ = lean_array_get_size(v___y_2132_);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_nat_dec_lt(v___y_2133_, v___x_2135_);
if (v___x_2137_ == 0)
{
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___x_2111_);
return v___x_2136_;
}
else
{
size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = lean_usize_of_nat(v___x_2135_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2111_, v___x_2112_, v___x_2113_, v___y_2132_, v___x_2138_, v___x_2139_, v___x_2136_);
lean_dec_ref(v___y_2132_);
return v___x_2140_;
}
}
}
v___jp_2141_:
{
if (lean_obj_tag(v_outputsRef_x3f_2115_) == 1)
{
lean_object* v_val_2142_; lean_object* v___x_2143_; lean_object* v_packages_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_config_2147_; lean_object* v_toLeanConfig_2148_; lean_object* v_platformIndependent_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_val_2142_ = lean_ctor_get(v_outputsRef_x3f_2115_, 0);
v___x_2143_ = lean_st_ref_get(v_val_2142_);
v_packages_2144_ = lean_ctor_get(v_ws_2114_, 4);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_array_fget_borrowed(v_packages_2144_, v___x_2145_);
v_config_2147_ = lean_ctor_get(v___x_2146_, 6);
v_toLeanConfig_2148_ = lean_ctor_get(v_config_2147_, 1);
v_platformIndependent_2149_ = lean_ctor_get(v_toLeanConfig_2148_, 10);
v___x_2150_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_2151_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_2149_, v___x_2150_);
v___x_2152_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_2153_ = l_Lake_CacheMap_writeFile(v_outputsFile_2117_, v___x_2143_, v___x_2151_, v___x_2152_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 2);
v___x_2155_ = lean_array_get_size(v_a_2154_);
v___x_2156_ = lean_nat_dec_eq(v___x_2155_, v___x_2145_);
if (v___x_2156_ == 0)
{
if (v_isVerbose_2118_ == 0)
{
lean_dec(v_a_2154_);
lean_dec_ref(v_out_2116_);
lean_dec_ref(v___x_2111_);
goto v___jp_2120_;
}
else
{
lean_object* v_putStr_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_putStr_2157_ = lean_ctor_get(v_out_2116_, 4);
lean_inc_ref(v_putStr_2157_);
lean_dec_ref(v_out_2116_);
v___x_2158_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_2159_ = lean_apply_2(v_putStr_2157_, v___x_2158_, lean_box(0));
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref_known(v___x_2159_, 1);
v___y_2123_ = v_a_2154_;
v___y_2124_ = v___x_2145_;
goto v___jp_2122_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2162_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2163_ = lean_unsigned_to_nat(82u);
v___x_2164_ = lean_unsigned_to_nat(4u);
v___x_2165_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2166_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2167_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2166_, v_isVerbose_2118_);
v___x_2168_ = lean_string_append(v___x_2165_, v___x_2167_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2170_ = lean_string_append(v___x_2168_, v___x_2169_);
v___x_2171_ = lean_io_error_to_string(v_a_2160_);
v___x_2172_ = lean_string_append(v___x_2170_, v___x_2171_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2174_ = lean_string_append(v___x_2172_, v___x_2173_);
v___x_2175_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_2176_ = lean_string_append(v___x_2174_, v___x_2175_);
v___x_2177_ = l_mkPanicMessageWithDecl(v___x_2161_, v___x_2162_, v___x_2163_, v___x_2164_, v___x_2176_);
lean_dec_ref(v___x_2176_);
v___x_2178_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2177_);
v___y_2123_ = v_a_2154_;
v___y_2124_ = v___x_2145_;
goto v___jp_2122_;
}
}
}
else
{
lean_dec(v_a_2154_);
lean_dec_ref(v_out_2116_);
lean_dec_ref(v___x_2111_);
goto v___jp_2120_;
}
}
else
{
lean_object* v_a_2179_; lean_object* v_putStr_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_a_2179_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2153_, 2);
v_putStr_2180_ = lean_ctor_get(v_out_2116_, 4);
lean_inc_ref(v_putStr_2180_);
lean_dec_ref(v_out_2116_);
v___x_2181_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_2182_ = lean_apply_2(v_putStr_2180_, v___x_2181_, lean_box(0));
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_dec_ref_known(v___x_2182_, 1);
v___y_2132_ = v_a_2179_;
v___y_2133_ = v___x_2145_;
goto v___jp_2131_;
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2185_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2186_ = lean_unsigned_to_nat(82u);
v___x_2187_ = lean_unsigned_to_nat(4u);
v___x_2188_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2189_ = lean_io_error_to_string(v_a_2183_);
v___x_2190_ = lean_string_append(v___x_2188_, v___x_2189_);
lean_dec_ref(v___x_2189_);
v___x_2191_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2192_ = lean_string_append(v___x_2190_, v___x_2191_);
v___x_2193_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_2194_ = lean_string_append(v___x_2192_, v___x_2193_);
v___x_2195_ = l_mkPanicMessageWithDecl(v___x_2184_, v___x_2185_, v___x_2186_, v___x_2187_, v___x_2194_);
lean_dec_ref(v___x_2194_);
v___x_2196_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2195_);
v___y_2132_ = v_a_2179_;
v___y_2133_ = v___x_2145_;
goto v___jp_2131_;
}
}
}
else
{
lean_object* v_putStr_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec_ref(v_outputsFile_2117_);
lean_dec_ref(v___x_2111_);
v_putStr_2197_ = lean_ctor_get(v_out_2116_, 4);
lean_inc_ref(v_putStr_2197_);
lean_dec_ref(v_out_2116_);
v___x_2198_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_2199_ = lean_apply_2(v_putStr_2197_, v___x_2198_, lean_box(0));
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
return v_a_2200_;
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_a_2201_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2201_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2202_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2203_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2204_ = lean_unsigned_to_nat(82u);
v___x_2205_ = lean_unsigned_to_nat(4u);
v___x_2206_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2207_ = lean_io_error_to_string(v_a_2201_);
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2210_ = lean_string_append(v___x_2208_, v___x_2209_);
v___x_2211_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15);
v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
v___x_2213_ = l_mkPanicMessageWithDecl(v___x_2202_, v___x_2203_, v___x_2204_, v___x_2205_, v___x_2212_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2213_);
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2226_, lean_object* v___x_2227_, lean_object* v___x_2228_, lean_object* v_ws_2229_, lean_object* v_outputsRef_x3f_2230_, lean_object* v_out_2231_, lean_object* v_outputsFile_2232_, lean_object* v_isVerbose_2233_, lean_object* v_a_2234_){
_start:
{
uint8_t v___x_1177__boxed_2235_; uint8_t v___x_1178__boxed_2236_; uint8_t v_isVerbose_boxed_2237_; lean_object* v_res_2238_; 
v___x_1177__boxed_2235_ = lean_unbox(v___x_2227_);
v___x_1178__boxed_2236_ = lean_unbox(v___x_2228_);
v_isVerbose_boxed_2237_ = lean_unbox(v_isVerbose_2233_);
v_res_2238_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2226_, v___x_1177__boxed_2235_, v___x_1178__boxed_2236_, v_ws_2229_, v_outputsRef_x3f_2230_, v_out_2231_, v_outputsFile_2232_, v_isVerbose_boxed_2237_);
lean_dec(v_outputsRef_x3f_2230_);
lean_dec_ref(v_ws_2229_);
return v_res_2238_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = 3;
v___x_2240_ = lean_uint32_to_uint8(v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2241_, lean_object* v_bctx_2242_, lean_object* v_mctx_2243_, lean_object* v_result_2244_){
_start:
{
lean_object* v___y_2247_; lean_object* v_out_2250_; uint8_t v_outLv_2251_; uint8_t v_useAnsi_2252_; lean_object* v_toMonitorResult_2253_; lean_object* v_out_2254_; lean_object* v___x_2255_; uint8_t v_noBuild_2256_; uint8_t v_verbosity_2257_; lean_object* v_outputsFile_x3f_2258_; 
v_out_2250_ = lean_ctor_get(v_mctx_2243_, 1);
lean_inc_ref_n(v_out_2250_, 2);
v_outLv_2251_ = lean_ctor_get_uint8(v_mctx_2243_, sizeof(void*)*4);
v_useAnsi_2252_ = lean_ctor_get_uint8(v_mctx_2243_, sizeof(void*)*4 + 4);
lean_dec_ref(v_mctx_2243_);
v_toMonitorResult_2253_ = lean_ctor_get(v_result_2244_, 0);
lean_inc_ref_n(v_toMonitorResult_2253_, 2);
v_out_2254_ = lean_ctor_get(v_result_2244_, 1);
lean_inc_ref(v_out_2254_);
lean_dec_ref(v_result_2244_);
v___x_2255_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2241_, v_out_2250_, v_toMonitorResult_2253_);
v_noBuild_2256_ = lean_ctor_get_uint8(v_cfg_2241_, sizeof(void*)*4 + 2);
v_verbosity_2257_ = lean_ctor_get_uint8(v_cfg_2241_, sizeof(void*)*4 + 4);
v_outputsFile_x3f_2258_ = lean_ctor_get(v_cfg_2241_, 1);
lean_inc(v_outputsFile_x3f_2258_);
lean_dec_ref(v_cfg_2241_);
if (lean_obj_tag(v_outputsFile_x3f_2258_) == 1)
{
lean_object* v_val_2273_; lean_object* v_toContext_2274_; lean_object* v_outputsRef_x3f_2275_; uint8_t v___y_2277_; 
v_val_2273_ = lean_ctor_get(v_outputsFile_x3f_2258_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v_outputsFile_x3f_2258_, 1);
v_toContext_2274_ = lean_ctor_get(v_bctx_2242_, 1);
v_outputsRef_x3f_2275_ = lean_ctor_get(v_bctx_2242_, 5);
if (v_verbosity_2257_ == 2)
{
uint8_t v___x_2279_; 
v___x_2279_ = 1;
v___y_2277_ = v___x_2279_;
goto v___jp_2276_;
}
else
{
uint8_t v___x_2280_; 
v___x_2280_ = 0;
v___y_2277_ = v___x_2280_;
goto v___jp_2276_;
}
v___jp_2276_:
{
lean_object* v___x_2278_; 
lean_inc_ref(v_out_2250_);
v___x_2278_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2250_, v_outLv_2251_, v_useAnsi_2252_, v_toContext_2274_, v_outputsRef_x3f_2275_, v_out_2250_, v_val_2273_, v___y_2277_);
goto v___jp_2259_;
}
}
else
{
lean_dec(v_outputsFile_x3f_2258_);
lean_dec_ref(v_out_2250_);
goto v___jp_2259_;
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_mk_io_user_error(v___y_2247_);
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
v___jp_2259_:
{
if (lean_obj_tag(v_out_2254_) == 0)
{
if (v_noBuild_2256_ == 0)
{
lean_object* v_a_2260_; 
lean_dec_ref(v_toMonitorResult_2253_);
v_a_2260_ = lean_ctor_get(v_out_2254_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v_out_2254_, 1);
v___y_2247_ = v_a_2260_;
goto v___jp_2246_;
}
else
{
uint8_t v_wantsRebuild_2261_; 
v_wantsRebuild_2261_ = lean_ctor_get_uint8(v_toMonitorResult_2253_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2253_);
if (v_wantsRebuild_2261_ == 0)
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v_out_2254_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v_out_2254_, 1);
v___y_2247_ = v_a_2262_;
goto v___jp_2246_;
}
else
{
uint8_t v___x_2263_; lean_object* v___x_2264_; 
lean_dec_ref_known(v_out_2254_, 1);
v___x_2263_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2264_ = lean_io_exit(v___x_2263_);
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v_toMonitorResult_2253_);
v_a_2265_ = lean_ctor_get(v_out_2254_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_out_2254_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v_out_2254_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v_out_2254_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set_tag(v___x_2267_, 0);
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2281_, lean_object* v_bctx_2282_, lean_object* v_mctx_2283_, lean_object* v_result_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2281_, v_bctx_2282_, v_mctx_2283_, v_result_2284_);
lean_dec_ref(v_bctx_2282_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2287_, lean_object* v_cfg_2288_, lean_object* v_bctx_2289_, lean_object* v_mctx_2290_, lean_object* v_result_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2288_, v_bctx_2289_, v_mctx_2290_, v_result_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_cfg_2295_, lean_object* v_bctx_2296_, lean_object* v_mctx_2297_, lean_object* v_result_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2294_, v_cfg_2295_, v_bctx_2296_, v_mctx_2297_, v_result_2298_);
lean_dec_ref(v_bctx_2296_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2301_, lean_object* v_build_2302_, lean_object* v_cfg_2303_, lean_object* v_caption_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_cancelTk_x3f_2309_; uint8_t v_failFast_2315_; 
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2307_ = lean_st_mk_ref(v___x_2306_);
v_failFast_2315_ = lean_ctor_get_uint8(v_cfg_2303_, sizeof(void*)*4 + 3);
if (v_failFast_2315_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_box(0);
v_cancelTk_x3f_2309_ = v___x_2316_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = l_IO_CancelToken_new();
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
v_cancelTk_x3f_2309_ = v___x_2318_;
goto v___jp_2308_;
}
v___jp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_inc(v_cancelTk_x3f_2309_);
lean_inc(v___x_2307_);
v___x_2310_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2303_, v___x_2307_, v_cancelTk_x3f_2309_);
lean_inc_ref(v_cfg_2303_);
v___x_2311_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2301_, v_cfg_2303_, v___x_2307_, v_cancelTk_x3f_2309_);
v___x_2312_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2311_, v_build_2302_, v_caption_2304_);
v___x_2313_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2310_, v___x_2312_);
v___x_2314_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2303_, v___x_2311_, v___x_2310_, v___x_2313_);
lean_dec_ref(v___x_2311_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2319_, lean_object* v_build_2320_, lean_object* v_cfg_2321_, lean_object* v_caption_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2319_, v_build_2320_, v_cfg_2321_, v_caption_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2325_, lean_object* v_ws_2326_, lean_object* v_build_2327_, lean_object* v_cfg_2328_, lean_object* v_caption_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2326_, v_build_2327_, v_cfg_2328_, v_caption_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2332_, lean_object* v_ws_2333_, lean_object* v_build_2334_, lean_object* v_cfg_2335_, lean_object* v_caption_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2332_, v_ws_2333_, v_build_2334_, v_cfg_2335_, v_caption_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2342_, lean_object* v_job_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v_out_2346_; 
v___x_2345_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2342_, v_job_2343_);
v_out_2346_ = lean_ctor_get(v___x_2345_, 1);
lean_inc_ref(v_out_2346_);
if (lean_obj_tag(v_out_2346_) == 0)
{
lean_object* v_toMonitorResult_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2362_; 
v_toMonitorResult_2347_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v___x_2345_, 1);
lean_dec(v_unused_2363_);
v___x_2349_ = v___x_2345_;
v_isShared_2350_ = v_isSharedCheck_2362_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_toMonitorResult_2347_);
lean_dec(v___x_2345_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2362_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2361_; 
v_a_2351_ = lean_ctor_get(v_out_2346_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_out_2346_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2353_ = v_out_2346_;
v_isShared_2354_ = v_isSharedCheck_2361_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v_out_2346_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2361_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v___x_2356_);
v___x_2358_ = v___x_2349_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_toMonitorResult_2347_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2387_; 
v_a_2364_ = lean_ctor_get(v_out_2346_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_out_2346_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2366_ = v_out_2346_;
v_isShared_2367_ = v_isSharedCheck_2387_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v_out_2346_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2387_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_toMonitorResult_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2385_; 
v_toMonitorResult_2368_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2345_, 1);
lean_dec(v_unused_2386_);
v___x_2370_ = v___x_2345_;
v_isShared_2371_ = v_isSharedCheck_2385_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_toMonitorResult_2368_);
lean_dec(v___x_2345_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2385_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_task_2372_; lean_object* v___x_2373_; 
v_task_2372_ = lean_ctor_get(v_a_2364_, 0);
lean_inc_ref(v_task_2372_);
lean_dec(v_a_2364_);
v___x_2373_ = lean_io_wait(v_task_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 2);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v_a_2374_);
v___x_2376_ = v___x_2366_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_2376_);
v___x_2378_ = v___x_2370_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_toMonitorResult_2368_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec_ref_known(v___x_2373_, 2);
lean_del_object(v___x_2366_);
v___x_2381_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___x_2381_);
v___x_2383_ = v___x_2370_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_toMonitorResult_2368_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2388_, lean_object* v_job_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2388_, v_job_2389_);
lean_dec_ref(v_mctx_2388_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2392_, lean_object* v_mctx_2393_, lean_object* v_job_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2393_, v_job_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_mctx_2398_, lean_object* v_job_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2397_, v_mctx_2398_, v_job_2399_);
lean_dec_ref(v_mctx_2398_);
return v_res_2401_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2415_, lean_object* v_build_2416_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_out_2429_; 
v___x_2418_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2419_ = lean_st_mk_ref(v___x_2418_);
v___x_2420_ = 0;
v___x_2421_ = 1;
v___x_2422_ = lean_box(0);
v___x_2423_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2419_);
v___x_2424_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2423_, v___x_2419_, v___x_2422_);
v___x_2425_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2415_, v___x_2423_, v___x_2419_, v___x_2422_);
v___x_2426_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2427_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2425_, v_build_2416_, v___x_2426_);
lean_dec_ref(v___x_2425_);
v___x_2428_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2424_, v___x_2427_);
lean_dec_ref(v___x_2424_);
v_out_2429_ = lean_ctor_get(v___x_2428_, 1);
lean_inc_ref(v_out_2429_);
lean_dec_ref(v___x_2428_);
if (lean_obj_tag(v_out_2429_) == 0)
{
lean_dec_ref_known(v_out_2429_, 1);
return v___x_2420_;
}
else
{
lean_dec_ref_known(v_out_2429_, 1);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2430_, lean_object* v_build_2431_, lean_object* v_a_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2430_, v_build_2431_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2435_, lean_object* v_ws_2436_, lean_object* v_build_2437_){
_start:
{
uint8_t v___x_2439_; 
v___x_2439_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2436_, v_build_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2440_, lean_object* v_ws_2441_, lean_object* v_build_2442_, lean_object* v_a_2443_){
_start:
{
uint8_t v_res_2444_; lean_object* v_r_2445_; 
v_res_2444_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2440_, v_ws_2441_, v_build_2442_);
v_r_2445_ = lean_box(v_res_2444_);
return v_r_2445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2446_, lean_object* v_build_2447_, lean_object* v_cfg_2448_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_cancelTk_x3f_2453_; uint8_t v_failFast_2460_; 
v___x_2450_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2451_ = lean_st_mk_ref(v___x_2450_);
v_failFast_2460_ = lean_ctor_get_uint8(v_cfg_2448_, sizeof(void*)*4 + 3);
if (v_failFast_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_box(0);
v_cancelTk_x3f_2453_ = v___x_2461_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = l_IO_CancelToken_new();
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
v_cancelTk_x3f_2453_ = v___x_2463_;
goto v___jp_2452_;
}
v___jp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_inc(v_cancelTk_x3f_2453_);
lean_inc(v___x_2451_);
v___x_2454_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2448_, v___x_2451_, v_cancelTk_x3f_2453_);
lean_inc_ref(v_cfg_2448_);
v___x_2455_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2446_, v_cfg_2448_, v___x_2451_, v_cancelTk_x3f_2453_);
v___x_2456_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2457_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2455_, v_build_2447_, v___x_2456_);
v___x_2458_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2454_, v___x_2457_);
v___x_2459_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2448_, v___x_2455_, v___x_2454_, v___x_2458_);
lean_dec_ref(v___x_2455_);
return v___x_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2464_, lean_object* v_build_2465_, lean_object* v_cfg_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lake_Workspace_runBuild___redArg(v_ws_2464_, v_build_2465_, v_cfg_2466_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2469_, lean_object* v_ws_2470_, lean_object* v_build_2471_, lean_object* v_cfg_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lake_Workspace_runBuild___redArg(v_ws_2470_, v_build_2471_, v_cfg_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_ws_2476_, lean_object* v_build_2477_, lean_object* v_cfg_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lake_Workspace_runBuild(v_00_u03b1_2475_, v_ws_2476_, v_build_2477_, v_cfg_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2481_, lean_object* v_cfg_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; 
lean_inc(v_a_2483_);
v___x_2485_ = l_Lake_Workspace_runBuild___redArg(v_a_2483_, v_build_2481_, v_cfg_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2486_, lean_object* v_cfg_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lake_runBuild___redArg(v_build_2486_, v_cfg_2487_, v_a_2488_);
lean_dec(v_a_2488_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2491_, lean_object* v_build_2492_, lean_object* v_cfg_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___x_2496_; 
lean_inc(v_a_2494_);
v___x_2496_ = l_Lake_Workspace_runBuild___redArg(v_a_2494_, v_build_2492_, v_cfg_2493_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_build_2498_, lean_object* v_cfg_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lake_runBuild(v_00_u03b1_2497_, v_build_2498_, v_cfg_2499_, v_a_2500_);
lean_dec(v_a_2500_);
return v_res_2502_;
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
