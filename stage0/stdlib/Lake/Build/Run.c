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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_Workspace_checkNoBuild___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_checkNoBuild___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 0, 0, 0, 0)}};
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
v_outLv_52_ = lean_ctor_get_uint8(v_ctx_50_, sizeof(void*)*3);
v_useAnsi_53_ = lean_ctor_get_uint8(v_ctx_50_, sizeof(void*)*3 + 4);
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
v___x_146_ = lean_unsigned_to_nat(78u);
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
v___x_187_ = lean_unsigned_to_nat(78u);
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
lean_object* v___x_228_; lean_object* v___x_7445__overap_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_7445__overap_229_ = lean_panic_fn_borrowed(v___x_228_, v_msg_226_);
v___x_230_ = lean_apply_1(v___x_7445__overap_229_, lean_box(0));
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
v_showProgress_250_ = lean_ctor_get_uint8(v_a_244_, sizeof(void*)*3 + 5);
if (v_showProgress_250_ == 0)
{
goto v___jp_247_;
}
else
{
uint8_t v_useAnsi_251_; 
v_useAnsi_251_ = lean_ctor_get_uint8(v_a_244_, sizeof(void*)*3 + 4);
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
v___x_304_ = lean_unsigned_to_nat(78u);
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
uint8_t v___y_13747__boxed_423_; uint8_t v_useAnsi_13748__boxed_424_; size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v___y_13747__boxed_423_ = lean_unbox(v___y_415_);
v_useAnsi_13748__boxed_424_ = lean_unbox(v_useAnsi_416_);
v_i_boxed_425_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_414_, v___y_13747__boxed_423_, v_useAnsi_13748__boxed_424_, v_as_417_, v_i_boxed_425_, v_stop_boxed_426_, v_b_420_, v___y_421_);
lean_dec_ref(v_as_417_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___y_440_; lean_object* v___y_444_; lean_object* v_val_445_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_jobNo_455_; lean_object* v_totalJobs_456_; uint8_t v_wantsRebuild_457_; lean_object* v_failures_458_; lean_object* v_resetCtrl_459_; lean_object* v_lastUpdate_460_; lean_object* v_spinnerIdx_461_; lean_object* v_out_462_; uint8_t v_outLv_463_; uint8_t v_failLv_464_; uint8_t v_minAction_465_; uint8_t v_showOptional_466_; uint8_t v_useAnsi_467_; uint8_t v_showProgress_468_; uint8_t v_showTime_469_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___y_476_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___y_559_; lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; uint8_t v___y_565_; lean_object* v___y_566_; lean_object* v_task_568_; lean_object* v_caption_569_; uint8_t v_optional_570_; uint8_t v___y_572_; lean_object* v___y_573_; uint8_t v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; uint8_t v___y_577_; lean_object* v___y_578_; uint8_t v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; uint32_t v___y_583_; lean_object* v___y_584_; uint8_t v___y_607_; lean_object* v___y_608_; uint8_t v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; uint8_t v___y_612_; lean_object* v___y_613_; uint8_t v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint32_t v___y_618_; uint8_t v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; uint8_t v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; uint32_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_641_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; uint32_t v___y_652_; uint8_t v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; lean_object* v___y_672_; uint8_t v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; uint8_t v___y_678_; lean_object* v___y_679_; uint8_t v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; uint8_t v___y_684_; uint8_t v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; uint8_t v___y_689_; uint8_t v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___y_712_; uint8_t v___y_713_; uint8_t v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; uint8_t v___y_717_; uint8_t v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; uint8_t v___y_737_; uint8_t v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; uint8_t v___y_742_; lean_object* v___y_743_; uint8_t v___y_744_; lean_object* v___y_745_; uint8_t v___y_746_; uint8_t v___y_751_; uint8_t v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; uint8_t v___y_755_; lean_object* v___y_756_; uint8_t v___y_757_; lean_object* v___y_758_; uint8_t v___y_759_; uint8_t v___y_765_; uint8_t v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; uint8_t v___y_770_; lean_object* v___y_771_; uint8_t v___y_772_; lean_object* v___y_777_; lean_object* v___x_788_; lean_object* v_a_789_; 
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
v_outLv_463_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3);
v_failLv_464_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 1);
v_minAction_465_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 2);
v_showOptional_466_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 3);
v_useAnsi_467_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 4);
v_showProgress_468_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 5);
v_showTime_469_ = lean_ctor_get_uint8(v_a_436_, sizeof(void*)*3 + 6);
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
v___x_477_ = lean_nat_dec_lt(v___y_475_, v___y_472_);
lean_dec(v___y_475_);
if (v___x_477_ == 0)
{
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
v___y_448_ = v___y_474_;
v___y_449_ = v___y_471_;
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
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_462_, v___y_476_, v_useAnsi_467_, v___y_473_, v___x_479_, v___x_480_, v___x_478_, v___y_471_);
lean_dec_ref(v___y_473_);
v_snd_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_snd_482_);
lean_dec_ref(v___x_481_);
v___y_448_ = v___y_474_;
v___y_449_ = v_snd_482_;
goto v___jp_447_;
}
}
v___jp_483_:
{
if (v___y_486_ == 0)
{
lean_dec(v___y_490_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_485_);
v___y_448_ = v___y_489_;
v___y_449_ = v___y_484_;
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
v_out_502_ = lean_ctor_get(v___y_497_, 1);
v_jobNo_503_ = lean_ctor_get(v___y_493_, 0);
v_totalJobs_504_ = lean_ctor_get(v___y_493_, 1);
v_wantsRebuild_505_ = lean_ctor_get_uint8(v___y_493_, sizeof(void*)*6);
v_failures_506_ = lean_ctor_get(v___y_493_, 2);
v_resetCtrl_507_ = lean_ctor_get(v___y_493_, 3);
v_lastUpdate_508_ = lean_ctor_get(v___y_493_, 4);
v_spinnerIdx_509_ = lean_ctor_get(v___y_493_, 5);
v_isSharedCheck_555_ = !lean_is_exclusive(v___y_493_);
if (v_isSharedCheck_555_ == 0)
{
v___x_511_ = v___y_493_;
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
lean_dec(v___y_493_);
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
v___y_484_ = v___x_516_;
v___y_485_ = v___y_494_;
v___y_486_ = v___y_496_;
v___y_487_ = v___y_495_;
v___y_488_ = v___y_498_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_499_;
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
v___x_527_ = lean_unsigned_to_nat(78u);
v___x_528_ = lean_unsigned_to_nat(4u);
v___x_529_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_530_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc(v___y_499_);
v___x_532_ = l_Lean_Name_num___override(v___x_531_, v___y_499_);
v___x_533_ = l_Lean_Name_str___override(v___x_532_, v___x_530_);
v___x_534_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_535_ = l_Lean_Name_str___override(v___x_533_, v___x_534_);
v___x_536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_535_, v___y_500_);
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
lean_inc_n(v___y_499_, 2);
v___x_548_ = l_Std_Format_pretty(v___x_546_, v___x_547_, v___y_499_, v___y_499_);
v___x_549_ = lean_string_append(v___x_543_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_mkPanicMessageWithDecl(v___x_525_, v___x_526_, v___x_527_, v___x_528_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_550_);
v___y_484_ = v___x_516_;
v___y_485_ = v___y_494_;
v___y_486_ = v___y_496_;
v___y_487_ = v___y_495_;
v___y_488_ = v___y_498_;
v___y_489_ = v___y_497_;
v___y_490_ = v___y_499_;
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
v___y_497_ = v___y_562_;
v___y_498_ = v___y_561_;
v___y_499_ = v___y_564_;
v___y_500_ = v___y_565_;
v___y_501_ = v___x_567_;
goto v___jp_492_;
}
v___jp_571_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_586_ = lean_string_push(v___x_585_, v___y_583_);
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
v___x_597_ = lean_string_append(v___x_596_, v___y_581_);
v___x_598_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_599_ = lean_string_append(v___x_597_, v___x_598_);
v___x_600_ = lean_string_append(v___x_599_, v___y_582_);
lean_dec_ref(v___y_582_);
v___x_601_ = lean_string_append(v___x_600_, v___x_598_);
v___x_602_ = lean_string_append(v___x_601_, v_caption_569_);
lean_dec_ref(v_caption_569_);
v___x_603_ = lean_string_append(v___x_602_, v___y_584_);
lean_dec_ref(v___y_584_);
if (v_useAnsi_467_ == 0)
{
v___y_493_ = v___y_578_;
v___y_494_ = v___y_573_;
v___y_495_ = v___y_575_;
v___y_496_ = v___y_574_;
v___y_497_ = v___y_580_;
v___y_498_ = v___y_579_;
v___y_499_ = v___y_576_;
v___y_500_ = v___y_577_;
v___y_501_ = v___x_603_;
goto v___jp_492_;
}
else
{
if (v___y_574_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_557_ = v___y_578_;
v___y_558_ = v___y_573_;
v___y_559_ = v___y_574_;
v___y_560_ = v___y_575_;
v___y_561_ = v___y_579_;
v___y_562_ = v___y_580_;
v___y_563_ = v___x_603_;
v___y_564_ = v___y_576_;
v___y_565_ = v___y_577_;
v___y_566_ = v___x_604_;
goto v___jp_556_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = l_Lake_LogLevel_ansiColor(v___y_572_);
v___y_557_ = v___y_578_;
v___y_558_ = v___y_573_;
v___y_559_ = v___y_574_;
v___y_560_ = v___y_575_;
v___y_561_ = v___y_579_;
v___y_562_ = v___y_580_;
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
lean_dec(v___y_627_);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_623_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_625_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_628_;
v___y_614_ = v___y_629_;
v___y_615_ = v___y_630_;
v___y_616_ = v___y_633_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
goto v___jp_606_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v___y_625_, v___y_627_);
if (v___x_634_ == 0)
{
lean_dec(v___y_627_);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_623_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_625_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_628_;
v___y_614_ = v___y_629_;
v___y_615_ = v___y_630_;
v___y_616_ = v___y_633_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_632_;
goto v___jp_606_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_636_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_627_);
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___y_572_ = v___y_621_;
v___y_573_ = v___y_622_;
v___y_574_ = v___y_623_;
v___y_575_ = v___y_624_;
v___y_576_ = v___y_625_;
v___y_577_ = v___y_626_;
v___y_578_ = v___y_628_;
v___y_579_ = v___y_629_;
v___y_580_ = v___y_630_;
v___y_581_ = v___y_633_;
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
v___y_621_ = v___y_642_;
v___y_622_ = v___y_643_;
v___y_623_ = v___y_645_;
v___y_624_ = v___y_644_;
v___y_625_ = v___y_649_;
v___y_626_ = v___y_650_;
v___y_627_ = v___y_651_;
v___y_628_ = v___y_641_;
v___y_629_ = v___y_647_;
v___y_630_ = v___y_646_;
v___y_631_ = v___y_648_;
v___y_632_ = v___y_652_;
v___y_633_ = v___x_653_;
goto v___jp_620_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_621_ = v___y_642_;
v___y_622_ = v___y_643_;
v___y_623_ = v___y_645_;
v___y_624_ = v___y_644_;
v___y_625_ = v___y_649_;
v___y_626_ = v___y_650_;
v___y_627_ = v___y_651_;
v___y_628_ = v___y_641_;
v___y_629_ = v___y_647_;
v___y_630_ = v___y_646_;
v___y_631_ = v___y_648_;
v___y_632_ = v___y_652_;
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
lean_dec(v___y_666_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
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
if (v___y_665_ == 0)
{
lean_dec(v___y_666_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_658_;
goto v___jp_439_;
}
else
{
lean_object* v___x_667_; uint32_t v___x_668_; 
v___x_667_ = l_Lake_JobAction_verb(v___y_663_, v___y_656_);
v___x_668_ = 10004;
v___y_641_ = v___y_658_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_659_;
v___y_644_ = v___y_660_;
v___y_645_ = v___y_661_;
v___y_646_ = v___y_662_;
v___y_647_ = v___y_663_;
v___y_648_ = v___x_667_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_666_;
v___y_652_ = v___x_668_;
goto v___jp_640_;
}
}
else
{
lean_dec(v___y_666_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
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
v___x_669_ = l_Lake_JobAction_verb(v___y_663_, v___y_656_);
v___x_670_ = l_Lake_LogLevel_icon(v___y_657_);
v___y_641_ = v___y_658_;
v___y_642_ = v___y_657_;
v___y_643_ = v___y_659_;
v___y_644_ = v___y_660_;
v___y_645_ = v___y_661_;
v___y_646_ = v___y_662_;
v___y_647_ = v___y_663_;
v___y_648_ = v___x_669_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_661_;
v___y_651_ = v___y_666_;
v___y_652_ = v___x_670_;
goto v___jp_640_;
}
}
v___jp_671_:
{
if (v_optional_570_ == 0)
{
v___y_656_ = v___y_673_;
v___y_657_ = v___y_674_;
v___y_658_ = v___y_672_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_676_;
v___y_661_ = v___y_682_;
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
lean_dec(v___y_681_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v_caption_569_);
lean_dec(v_totalJobs_456_);
lean_dec(v_jobNo_455_);
v___y_440_ = v___y_672_;
goto v___jp_439_;
}
else
{
v___y_656_ = v___y_673_;
v___y_657_ = v___y_674_;
v___y_658_ = v___y_672_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_676_;
v___y_661_ = v___y_682_;
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
if (v___y_689_ == 0)
{
if (v___y_690_ == 0)
{
v___y_672_ = v___y_695_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_694_;
v___y_678_ = v___y_689_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_692_;
v___y_681_ = v___y_693_;
v___y_682_ = v___y_690_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___y_695_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_694_;
v___y_678_ = v___y_689_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_692_;
v___y_681_ = v___y_693_;
v___y_682_ = v___y_684_;
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
v___y_672_ = v___x_708_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_694_;
v___y_678_ = v___y_689_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_692_;
v___y_681_ = v___y_693_;
v___y_682_ = v___y_689_;
goto v___jp_671_;
}
}
}
else
{
v___y_672_ = v___y_695_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_694_;
v___y_678_ = v___y_689_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_692_;
v___y_681_ = v___y_693_;
v___y_682_ = v___y_689_;
goto v___jp_671_;
}
}
}
v___jp_711_:
{
if (v___y_720_ == 0)
{
v___y_684_ = v___y_712_;
v___y_685_ = v___y_713_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_722_;
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
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*6, v___y_720_);
v___y_684_ = v___y_712_;
v___y_685_ = v___y_713_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_722_;
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
v___y_685_ = v___y_713_;
v___y_686_ = v___y_714_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_716_;
v___y_689_ = v___y_717_;
v___y_690_ = v___y_718_;
v___y_691_ = v___y_719_;
v___y_692_ = v___y_722_;
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
v___x_747_ = l_Lake_instOrdJobAction_ord(v_minAction_465_, v___y_738_);
if (v___x_747_ == 2)
{
uint8_t v___x_748_; 
v___x_748_ = 0;
v___y_712_ = v___y_746_;
v___y_713_ = v___y_738_;
v___y_714_ = v___y_737_;
v___y_715_ = v___y_739_;
v___y_716_ = v___y_740_;
v___y_717_ = v___y_741_;
v___y_718_ = v___y_742_;
v___y_719_ = v___y_743_;
v___y_720_ = v___y_744_;
v___y_721_ = v___y_745_;
v___y_722_ = v___x_748_;
goto v___jp_711_;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 1;
v___y_712_ = v___y_746_;
v___y_713_ = v___y_738_;
v___y_714_ = v___y_737_;
v___y_715_ = v___y_739_;
v___y_716_ = v___y_740_;
v___y_717_ = v___y_741_;
v___y_718_ = v___y_742_;
v___y_719_ = v___y_743_;
v___y_720_ = v___y_744_;
v___y_721_ = v___y_745_;
v___y_722_ = v___x_749_;
goto v___jp_711_;
}
}
v___jp_750_:
{
uint8_t v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_strict_and(v___y_755_, v___y_759_);
v___x_761_ = l_Lake_instOrdLogLevel_ord(v_outLv_463_, v___y_752_);
if (v___x_761_ == 2)
{
uint8_t v___x_762_; 
v___x_762_ = 0;
v___y_737_ = v___y_752_;
v___y_738_ = v___y_751_;
v___y_739_ = v___y_753_;
v___y_740_ = v___y_754_;
v___y_741_ = v___x_760_;
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v___y_758_;
v___y_746_ = v___x_762_;
goto v___jp_736_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 1;
v___y_737_ = v___y_752_;
v___y_738_ = v___y_751_;
v___y_739_ = v___y_753_;
v___y_740_ = v___y_754_;
v___y_741_ = v___x_760_;
v___y_742_ = v___y_755_;
v___y_743_ = v___y_756_;
v___y_744_ = v___y_757_;
v___y_745_ = v___y_758_;
v___y_746_ = v___x_763_;
goto v___jp_736_;
}
}
v___jp_764_:
{
uint8_t v___x_773_; 
v___x_773_ = l_Lake_instOrdLogLevel_ord(v_failLv_464_, v___y_765_);
if (v___x_773_ == 2)
{
uint8_t v___x_774_; 
v___x_774_ = 0;
v___y_751_ = v___y_766_;
v___y_752_ = v___y_765_;
v___y_753_ = v___y_767_;
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
v___y_751_ = v___y_766_;
v___y_752_ = v___y_765_;
v___y_753_ = v___y_767_;
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
v___y_765_ = v___x_782_;
v___y_766_ = v_action_779_;
v___y_767_ = v___x_783_;
v___y_768_ = v_log_778_;
v___y_769_ = v___x_784_;
v___y_770_ = v_wantsRebuild_780_;
v___y_771_ = v_buildTime_781_;
v___y_772_ = v___x_786_;
goto v___jp_764_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = 0;
v___y_765_ = v___x_782_;
v___y_766_ = v_action_779_;
v___y_767_ = v___x_783_;
v___y_768_ = v_log_778_;
v___y_769_ = v___x_784_;
v___y_770_ = v_wantsRebuild_780_;
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
uint8_t v___y_14507__boxed_816_; uint8_t v_useAnsi_14508__boxed_817_; size_t v_i_boxed_818_; size_t v_stop_boxed_819_; lean_object* v_res_820_; 
v___y_14507__boxed_816_ = lean_unbox(v___y_807_);
v_useAnsi_14508__boxed_817_ = lean_unbox(v_useAnsi_808_);
v_i_boxed_818_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_stop_boxed_819_ = lean_unbox_usize(v_stop_811_);
lean_dec(v_stop_811_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_806_, v___y_14507__boxed_816_, v_useAnsi_14508__boxed_817_, v_as_809_, v_i_boxed_818_, v_stop_boxed_819_, v_b_812_, v___y_813_, v___y_814_);
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
lean_object* v___x_1003_; lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
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
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_array_get_size(v_snd_1007_);
v___x_1010_ = lean_nat_dec_lt(v___x_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_fst_1006_);
v___x_1011_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1000_, v_snd_1005_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
v_snd_1013_ = lean_ctor_get(v___x_1011_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1015_ = v___x_1011_;
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snd_1013_);
lean_inc(v_fst_1012_);
lean_dec(v___x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = lean_array_get_size(v_fst_1012_);
v___x_1018_ = lean_nat_dec_lt(v___x_1008_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec(v_fst_1012_);
lean_dec(v_snd_1007_);
v___x_1019_ = lean_box(0);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1019_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_1013_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_del_object(v___x_1015_);
v_new_998_ = v_fst_1012_;
v_unfinished_999_ = v_snd_1007_;
v_a_1001_ = v_snd_1013_;
goto _start;
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v_snd_1026_; lean_object* v___x_1027_; lean_object* v_snd_1028_; lean_object* v___x_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; 
v___x_1025_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1006_, v_snd_1007_, v_a_1000_, v_snd_1005_);
lean_dec(v_fst_1006_);
v_snd_1026_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_snd_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1000_, v_snd_1026_);
v_snd_1028_ = lean_ctor_get(v___x_1027_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1000_, v_snd_1028_);
v_fst_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_fst_1030_);
v_snd_1031_ = lean_ctor_get(v___x_1029_, 1);
lean_inc(v_snd_1031_);
lean_dec_ref(v___x_1029_);
v_new_998_ = v_fst_1030_;
v_unfinished_999_ = v_snd_1007_;
v_a_1001_ = v_snd_1031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* v_new_1033_, lean_object* v_unfinished_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_new_1033_, v_unfinished_1034_, v_a_1035_, v_a_1036_);
lean_dec_ref(v_a_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* v_init_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1114_; 
v___x_1043_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1040_, v_a_1041_);
v_fst_1044_ = lean_ctor_get(v___x_1043_, 0);
v_snd_1045_ = lean_ctor_get(v___x_1043_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1047_ = v___x_1043_;
v_isShared_1048_ = v_isSharedCheck_1114_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v___x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1114_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v_snd_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1112_; 
v___x_1049_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(v_fst_1044_, v_init_1039_, v_a_1040_, v_snd_1045_);
v_snd_1050_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v___x_1049_, 0);
lean_dec(v_unused_1113_);
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1112_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_snd_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1112_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_jobNo_1054_; lean_object* v_totalJobs_1055_; uint8_t v_wantsRebuild_1056_; lean_object* v_failures_1057_; lean_object* v_resetCtrl_1058_; lean_object* v_lastUpdate_1059_; lean_object* v_spinnerIdx_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1111_; 
v_jobNo_1054_ = lean_ctor_get(v_snd_1050_, 0);
v_totalJobs_1055_ = lean_ctor_get(v_snd_1050_, 1);
v_wantsRebuild_1056_ = lean_ctor_get_uint8(v_snd_1050_, sizeof(void*)*6);
v_failures_1057_ = lean_ctor_get(v_snd_1050_, 2);
v_resetCtrl_1058_ = lean_ctor_get(v_snd_1050_, 3);
v_lastUpdate_1059_ = lean_ctor_get(v_snd_1050_, 4);
v_spinnerIdx_1060_ = lean_ctor_get(v_snd_1050_, 5);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_snd_1050_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1062_ = v_snd_1050_;
v_isShared_1063_ = v_isSharedCheck_1111_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_spinnerIdx_1060_);
lean_inc(v_lastUpdate_1059_);
lean_inc(v_resetCtrl_1058_);
lean_inc(v_failures_1057_);
lean_inc(v_totalJobs_1055_);
lean_inc(v_jobNo_1054_);
lean_dec(v_snd_1050_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1111_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 3, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_jobNo_1054_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_totalJobs_1055_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_failures_1057_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_lastUpdate_1059_);
lean_ctor_set(v_reuseFailAlloc_1110_, 5, v_spinnerIdx_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*6, v_wantsRebuild_1056_);
v___x_1066_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v_val_1068_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_string_utf8_byte_size(v_resetCtrl_1058_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_nat_dec_eq(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v_out_1075_; lean_object* v_flush_1076_; lean_object* v_putStr_1077_; lean_object* v___x_1082_; 
lean_del_object(v___x_1047_);
v_out_1075_ = lean_ctor_get(v_a_1040_, 1);
v_flush_1076_ = lean_ctor_get(v_out_1075_, 0);
v_putStr_1077_ = lean_ctor_get(v_out_1075_, 4);
lean_inc_ref(v_putStr_1077_);
lean_inc_ref(v_resetCtrl_1058_);
v___x_1082_ = lean_apply_2(v_putStr_1077_, v_resetCtrl_1058_, lean_box(0));
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_dec_ref_known(v___x_1082_, 1);
lean_dec_ref(v_resetCtrl_1058_);
goto v___jp_1078_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1105_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1105_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1105_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1087_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1088_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1089_ = lean_unsigned_to_nat(78u);
v___x_1090_ = lean_unsigned_to_nat(4u);
v___x_1091_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1092_ = lean_io_error_to_string(v_a_1083_);
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
v___x_1096_ = l_String_quote(v_resetCtrl_1058_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
lean_ctor_set(v___x_1085_, 0, v___x_1096_);
v___x_1098_ = v___x_1085_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1099_ = l_Std_Format_defWidth;
v___x_1100_ = l_Std_Format_pretty(v___x_1098_, v___x_1099_, v___x_1073_, v___x_1073_);
v___x_1101_ = lean_string_append(v___x_1095_, v___x_1100_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = l_mkPanicMessageWithDecl(v___x_1087_, v___x_1088_, v___x_1089_, v___x_1090_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1102_);
goto v___jp_1078_;
}
}
}
v___jp_1078_:
{
lean_object* v___x_1079_; 
lean_inc_ref(v_flush_1076_);
v___x_1079_ = lean_apply_1(v_flush_1076_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_val_1068_ = v_a_1080_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1081_; 
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_box(0);
v_val_1068_ = v___x_1081_;
goto v___jp_1067_;
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec_ref(v_resetCtrl_1058_);
lean_del_object(v___x_1052_);
v___x_1106_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1066_);
lean_ctor_set(v___x_1047_, 0, v___x_1106_);
v___x_1108_ = v___x_1047_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1066_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
v___jp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___x_1066_);
lean_ctor_set(v___x_1052_, 0, v_val_1068_);
v___x_1070_ = v___x_1052_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_val_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1066_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* v_init_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_1115_, v_a_1116_, v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* v_self_1120_){
_start:
{
lean_object* v_failures_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_failures_1121_ = lean_ctor_get(v_self_1120_, 0);
v___x_1122_ = lean_array_get_size(v_failures_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_nat_dec_eq(v___x_1122_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* v_self_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_1125_);
lean_dec_ref(v_self_1125_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0(void){
_start:
{
uint8_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = 2;
v___x_1129_ = l_Lake_Verbosity_ctorIdx(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1130_, lean_object* v_jobs_1131_){
_start:
{
lean_object* v_toLogConfig_1133_; uint8_t v_verbosity_1134_; uint8_t v_failLv_1135_; uint8_t v_outLv_1136_; uint8_t v_ansiMode_1137_; lean_object* v_out_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; uint8_t v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1151_; 
v_toLogConfig_1133_ = lean_ctor_get(v_cfg_1130_, 0);
v_verbosity_1134_ = lean_ctor_get_uint8(v_cfg_1130_, sizeof(void*)*4 + 3);
v_failLv_1135_ = lean_ctor_get_uint8(v_toLogConfig_1133_, sizeof(void*)*1);
v_outLv_1136_ = lean_ctor_get_uint8(v_toLogConfig_1133_, sizeof(void*)*1 + 1);
v_ansiMode_1137_ = lean_ctor_get_uint8(v_toLogConfig_1133_, sizeof(void*)*1 + 2);
v_out_1138_ = lean_ctor_get(v_toLogConfig_1133_, 0);
v___x_1139_ = l_Lake_OutStream_get(v_out_1138_);
lean_inc_ref(v___x_1139_);
v___x_1140_ = l_Lake_AnsiMode_isEnabled(v___x_1139_, v_ansiMode_1137_);
v___x_1141_ = l_Lake_BuildConfig_showProgress(v_cfg_1130_);
v___x_1142_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1134_);
v___x_1143_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0, &l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0);
v___x_1144_ = lean_nat_dec_eq(v___x_1142_, v___x_1143_);
lean_dec(v___x_1142_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1153_; 
v___x_1153_ = 3;
v___y_1151_ = v___x_1153_;
goto v___jp_1150_;
}
else
{
uint8_t v___x_1154_; 
v___x_1154_ = 0;
v___y_1151_ = v___x_1154_;
goto v___jp_1150_;
}
v___jp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(100u);
v___x_1149_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v___x_1149_, 0, v_jobs_1131_);
lean_ctor_set(v___x_1149_, 1, v___x_1139_);
lean_ctor_set(v___x_1149_, 2, v___x_1148_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3, v_outLv_1136_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3 + 1, v_failLv_1135_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3 + 2, v___y_1146_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3 + 3, v___x_1144_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3 + 4, v___x_1140_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3 + 5, v___x_1141_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3 + 6, v___y_1147_);
return v___x_1149_;
}
v___jp_1150_:
{
if (v___x_1144_ == 0)
{
if (v___x_1140_ == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = 1;
v___y_1146_ = v___y_1151_;
v___y_1147_ = v___x_1152_;
goto v___jp_1145_;
}
else
{
v___y_1146_ = v___y_1151_;
v___y_1147_ = v___x_1144_;
goto v___jp_1145_;
}
}
else
{
v___y_1146_ = v___y_1151_;
v___y_1147_ = v___x_1144_;
goto v___jp_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1155_, lean_object* v_jobs_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1155_, v_jobs_1156_);
lean_dec_ref(v_cfg_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1159_, lean_object* v_initJobs_1160_, lean_object* v_initFailures_1161_, lean_object* v_resetCtrl_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_snd_1169_; lean_object* v_totalJobs_1170_; uint8_t v_wantsRebuild_1171_; lean_object* v_failures_1172_; lean_object* v___x_1173_; 
v___x_1164_ = lean_io_mono_ms_now();
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = 0;
v___x_1167_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
lean_ctor_set(v___x_1167_, 2, v_initFailures_1161_);
lean_ctor_set(v___x_1167_, 3, v_resetCtrl_1162_);
lean_ctor_set(v___x_1167_, 4, v___x_1164_);
lean_ctor_set(v___x_1167_, 5, v___x_1165_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*6, v___x_1166_);
v___x_1168_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1160_, v_ctx_1159_, v___x_1167_);
v_snd_1169_ = lean_ctor_get(v___x_1168_, 1);
lean_inc(v_snd_1169_);
lean_dec_ref(v___x_1168_);
v_totalJobs_1170_ = lean_ctor_get(v_snd_1169_, 1);
lean_inc(v_totalJobs_1170_);
v_wantsRebuild_1171_ = lean_ctor_get_uint8(v_snd_1169_, sizeof(void*)*6);
v_failures_1172_ = lean_ctor_get(v_snd_1169_, 2);
lean_inc_ref(v_failures_1172_);
lean_dec(v_snd_1169_);
v___x_1173_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1173_, 0, v_failures_1172_);
lean_ctor_set(v___x_1173_, 1, v_totalJobs_1170_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*2, v_wantsRebuild_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1174_, lean_object* v_initJobs_1175_, lean_object* v_initFailures_1176_, lean_object* v_resetCtrl_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1174_, v_initJobs_1175_, v_initFailures_1176_, v_resetCtrl_1177_);
lean_dec_ref(v_ctx_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1180_, lean_object* v_jobs_1181_, lean_object* v_out_1182_, uint8_t v_failLv_1183_, uint8_t v_outLv_1184_, uint8_t v_minAction_1185_, uint8_t v_showOptional_1186_, uint8_t v_useAnsi_1187_, uint8_t v_showProgress_1188_, uint8_t v_showTime_1189_, lean_object* v_resetCtrl_1190_, lean_object* v_initFailures_1191_, lean_object* v_updateFrequency_1192_){
_start:
{
lean_object* v_ctx_1194_; lean_object* v___x_1195_; 
v_ctx_1194_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v_ctx_1194_, 0, v_jobs_1181_);
lean_ctor_set(v_ctx_1194_, 1, v_out_1182_);
lean_ctor_set(v_ctx_1194_, 2, v_updateFrequency_1192_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3, v_outLv_1184_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3 + 1, v_failLv_1183_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3 + 2, v_minAction_1185_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3 + 3, v_showOptional_1186_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3 + 4, v_useAnsi_1187_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3 + 5, v_showProgress_1188_);
lean_ctor_set_uint8(v_ctx_1194_, sizeof(void*)*3 + 6, v_showTime_1189_);
v___x_1195_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1194_, v_initJobs_1180_, v_initFailures_1191_, v_resetCtrl_1190_);
lean_dec_ref_known(v_ctx_1194_, 3);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1196_, lean_object* v_jobs_1197_, lean_object* v_out_1198_, lean_object* v_failLv_1199_, lean_object* v_outLv_1200_, lean_object* v_minAction_1201_, lean_object* v_showOptional_1202_, lean_object* v_useAnsi_1203_, lean_object* v_showProgress_1204_, lean_object* v_showTime_1205_, lean_object* v_resetCtrl_1206_, lean_object* v_initFailures_1207_, lean_object* v_updateFrequency_1208_, lean_object* v_a_1209_){
_start:
{
uint8_t v_failLv_boxed_1210_; uint8_t v_outLv_boxed_1211_; uint8_t v_minAction_boxed_1212_; uint8_t v_showOptional_boxed_1213_; uint8_t v_useAnsi_boxed_1214_; uint8_t v_showProgress_boxed_1215_; uint8_t v_showTime_boxed_1216_; lean_object* v_res_1217_; 
v_failLv_boxed_1210_ = lean_unbox(v_failLv_1199_);
v_outLv_boxed_1211_ = lean_unbox(v_outLv_1200_);
v_minAction_boxed_1212_ = lean_unbox(v_minAction_1201_);
v_showOptional_boxed_1213_ = lean_unbox(v_showOptional_1202_);
v_useAnsi_boxed_1214_ = lean_unbox(v_useAnsi_1203_);
v_showProgress_boxed_1215_ = lean_unbox(v_showProgress_1204_);
v_showTime_boxed_1216_ = lean_unbox(v_showTime_1205_);
v_res_1217_ = l_Lake_monitorJobs(v_initJobs_1196_, v_jobs_1197_, v_out_1198_, v_failLv_boxed_1210_, v_outLv_boxed_1211_, v_minAction_boxed_1212_, v_showOptional_boxed_1213_, v_useAnsi_boxed_1214_, v_showProgress_boxed_1215_, v_showTime_boxed_1216_, v_resetCtrl_1206_, v_initFailures_1207_, v_updateFrequency_1208_);
return v_res_1217_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1218_; 
v___x_1218_ = 3;
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_apply_2(v_logger_1219_, v___y_1221_, lean_box(0));
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1224_, lean_object* v_x_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1224_, v_x_1225_, v___y_1226_);
return v_res_1228_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1239_ = l_String_quote(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Std_Format_defWidth;
v___x_1244_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1245_ = l_Std_Format_pretty(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1242_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_1248_ = l_String_quote(v___x_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_1250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = l_Std_Format_defWidth;
v___x_1253_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1254_ = l_Std_Format_pretty(v___x_1253_, v___x_1252_, v___x_1251_, v___x_1251_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_1257_ = l_String_quote(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_1259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = l_Std_Format_defWidth;
v___x_1262_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_1263_ = l_Std_Format_pretty(v___x_1262_, v___x_1261_, v___x_1260_, v___x_1260_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1265_, lean_object* v_ws_1266_, lean_object* v_outputsRef_x3f_1267_, lean_object* v_out_1268_, lean_object* v_outputsFile_1269_, uint8_t v_isVerbose_1270_){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___x_1378_; 
lean_inc_ref(v_logger_1265_);
v___f_1274_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1274_, 0, v_logger_1265_);
v___x_1275_ = l_instMonadBaseIO;
v___x_1378_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1266_);
if (v___x_1378_ == 0)
{
lean_object* v_packages_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_baseName_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_packages_1379_ = lean_ctor_get(v_ws_1266_, 4);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_array_fget_borrowed(v_packages_1379_, v___x_1380_);
v_baseName_1382_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_baseName_1382_);
v___x_1383_ = l_Lean_Name_toString(v_baseName_1382_, v___x_1378_);
v___x_1384_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16));
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
v___x_1386_ = 2;
v___x_1387_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*1, v___x_1386_);
v___x_1388_ = lean_apply_2(v_logger_1265_, v___x_1387_, lean_box(0));
goto v___jp_1297_;
}
else
{
lean_dec_ref(v_logger_1265_);
goto v___jp_1297_;
}
v___jp_1272_:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_box(0);
return v___x_1273_;
}
v___jp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_array_get_size(v___y_1278_);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_nat_dec_lt(v___y_1277_, v___x_1279_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___f_1274_);
return v___x_1280_;
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1374__overap_1284_; lean_object* v___x_1285_; 
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1279_);
v___x_1374__overap_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1275_, v___f_1274_, v___y_1278_, v___x_1282_, v___x_1283_, v___x_1280_);
v___x_1285_ = lean_apply_1(v___x_1374__overap_1284_, lean_box(0));
return v___x_1285_;
}
}
v___jp_1286_:
{
if (v_isVerbose_1270_ == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v___y_1288_);
lean_dec_ref(v___f_1274_);
v___x_1289_ = lean_box(0);
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1290_ = lean_array_get_size(v___y_1288_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_nat_dec_lt(v___y_1287_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_dec_ref(v___y_1288_);
lean_dec_ref(v___f_1274_);
return v___x_1291_;
}
else
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1305__overap_1295_; lean_object* v___x_1296_; 
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1290_);
v___x_1305__overap_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1275_, v___f_1274_, v___y_1288_, v___x_1293_, v___x_1294_, v___x_1291_);
v___x_1296_ = lean_apply_1(v___x_1305__overap_1295_, lean_box(0));
return v___x_1296_;
}
}
}
v___jp_1297_:
{
if (lean_obj_tag(v_outputsRef_x3f_1267_) == 1)
{
lean_object* v_val_1298_; lean_object* v___x_1299_; lean_object* v_packages_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_config_1303_; lean_object* v_toLeanConfig_1304_; lean_object* v_platformIndependent_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_val_1298_ = lean_ctor_get(v_outputsRef_x3f_1267_, 0);
v___x_1299_ = lean_st_ref_get(v_val_1298_);
v_packages_1300_ = lean_ctor_get(v_ws_1266_, 4);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_fget_borrowed(v_packages_1300_, v___x_1301_);
v_config_1303_ = lean_ctor_get(v___x_1302_, 6);
v_toLeanConfig_1304_ = lean_ctor_get(v_config_1303_, 1);
v_platformIndependent_1305_ = lean_ctor_get(v_toLeanConfig_1304_, 10);
v___f_1306_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1307_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
lean_inc(v_platformIndependent_1305_);
v___x_1308_ = l_Option_instBEq_beq___redArg(v___f_1306_, v_platformIndependent_1305_, v___x_1307_);
v___x_1309_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1310_ = l_Lake_CacheMap_writeFile(v_outputsFile_1269_, v___x_1299_, v___x_1308_, v___x_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 2);
v___x_1312_ = lean_array_get_size(v_a_1311_);
v___x_1313_ = lean_nat_dec_eq(v___x_1312_, v___x_1301_);
if (v___x_1313_ == 0)
{
if (v_isVerbose_1270_ == 0)
{
lean_dec(v_a_1311_);
lean_dec_ref(v___f_1274_);
lean_dec_ref(v_out_1268_);
goto v___jp_1272_;
}
else
{
lean_object* v_putStr_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_putStr_1314_ = lean_ctor_get(v_out_1268_, 4);
lean_inc_ref(v_putStr_1314_);
lean_dec_ref(v_out_1268_);
v___x_1315_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1316_ = lean_apply_2(v_putStr_1314_, v___x_1315_, lean_box(0));
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_dec_ref_known(v___x_1316_, 1);
v___y_1277_ = v___x_1301_;
v___y_1278_ = v_a_1311_;
goto v___jp_1276_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1569__overap_1336_; lean_object* v___x_1337_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1319_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1320_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1321_ = lean_unsigned_to_nat(78u);
v___x_1322_ = lean_unsigned_to_nat(4u);
v___x_1323_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1324_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1325_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1324_, v_isVerbose_1270_);
v___x_1326_ = lean_string_append(v___x_1323_, v___x_1325_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1328_ = lean_string_append(v___x_1326_, v___x_1327_);
v___x_1329_ = lean_io_error_to_string(v_a_1317_);
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1332_ = lean_string_append(v___x_1330_, v___x_1331_);
v___x_1333_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_1334_ = lean_string_append(v___x_1332_, v___x_1333_);
v___x_1335_ = l_mkPanicMessageWithDecl(v___x_1319_, v___x_1320_, v___x_1321_, v___x_1322_, v___x_1334_);
lean_dec_ref(v___x_1334_);
v___x_1569__overap_1336_ = l_panic___redArg(v___x_1318_, v___x_1335_);
v___x_1337_ = lean_apply_1(v___x_1569__overap_1336_, lean_box(0));
v___y_1277_ = v___x_1301_;
v___y_1278_ = v_a_1311_;
goto v___jp_1276_;
}
}
}
else
{
lean_dec(v_a_1311_);
lean_dec_ref(v___f_1274_);
lean_dec_ref(v_out_1268_);
goto v___jp_1272_;
}
}
else
{
lean_object* v_a_1338_; lean_object* v_putStr_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_a_1338_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1310_, 2);
v_putStr_1339_ = lean_ctor_get(v_out_1268_, 4);
lean_inc_ref(v_putStr_1339_);
lean_dec_ref(v_out_1268_);
v___x_1340_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_1341_ = lean_apply_2(v_putStr_1339_, v___x_1340_, lean_box(0));
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref_known(v___x_1341_, 1);
v___y_1287_ = v___x_1301_;
v___y_1288_ = v_a_1338_;
goto v___jp_1286_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1354__overap_1356_; lean_object* v___x_1357_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1343_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1344_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1345_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1346_ = lean_unsigned_to_nat(78u);
v___x_1347_ = lean_unsigned_to_nat(4u);
v___x_1348_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1349_ = lean_io_error_to_string(v_a_1342_);
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1352_ = lean_string_append(v___x_1350_, v___x_1351_);
v___x_1353_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_1354_ = lean_string_append(v___x_1352_, v___x_1353_);
v___x_1355_ = l_mkPanicMessageWithDecl(v___x_1344_, v___x_1345_, v___x_1346_, v___x_1347_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1354__overap_1356_ = l_panic___redArg(v___x_1343_, v___x_1355_);
v___x_1357_ = lean_apply_1(v___x_1354__overap_1356_, lean_box(0));
v___y_1287_ = v___x_1301_;
v___y_1288_ = v_a_1338_;
goto v___jp_1286_;
}
}
}
else
{
lean_object* v_putStr_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v___f_1274_);
lean_dec_ref(v_outputsFile_1269_);
v_putStr_1358_ = lean_ctor_get(v_out_1268_, 4);
lean_inc_ref(v_putStr_1358_);
lean_dec_ref(v_out_1268_);
v___x_1359_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_1360_ = lean_apply_2(v_putStr_1358_, v___x_1359_, lean_box(0));
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
return v_a_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1472__overap_1376_; lean_object* v___x_1377_; 
v_a_1362_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1363_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1364_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1365_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1366_ = lean_unsigned_to_nat(78u);
v___x_1367_ = lean_unsigned_to_nat(4u);
v___x_1368_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1369_ = lean_io_error_to_string(v_a_1362_);
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1372_ = lean_string_append(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15);
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
v___x_1375_ = l_mkPanicMessageWithDecl(v___x_1364_, v___x_1365_, v___x_1366_, v___x_1367_, v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1472__overap_1376_ = l_panic___redArg(v___x_1363_, v___x_1375_);
v___x_1377_ = lean_apply_1(v___x_1472__overap_1376_, lean_box(0));
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1389_, lean_object* v_ws_1390_, lean_object* v_outputsRef_x3f_1391_, lean_object* v_out_1392_, lean_object* v_outputsFile_1393_, lean_object* v_isVerbose_1394_, lean_object* v_a_1395_){
_start:
{
uint8_t v_isVerbose_boxed_1396_; lean_object* v_res_1397_; 
v_isVerbose_boxed_1396_ = lean_unbox(v_isVerbose_1394_);
v_res_1397_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1389_, v_ws_1390_, v_outputsRef_x3f_1391_, v_out_1392_, v_outputsFile_1393_, v_isVerbose_boxed_1396_);
lean_dec(v_outputsRef_x3f_1391_);
lean_dec_ref(v_ws_1390_);
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
lean_dec_ref_known(v___x_1417_, 1);
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
v___x_1423_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1424_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1425_ = lean_unsigned_to_nat(78u);
v___x_1426_ = lean_unsigned_to_nat(4u);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1429_ = lean_io_error_to_string(v_a_1419_);
v___x_1430_ = lean_string_append(v___x_1428_, v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1468_ = l_String_quote(v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Std_Format_defWidth;
v___x_1473_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1474_ = l_Std_Format_pretty(v___x_1473_, v___x_1472_, v___x_1471_, v___x_1471_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1475_, lean_object* v_out_1476_, lean_object* v_result_1477_){
_start:
{
uint8_t v___y_1480_; lean_object* v___y_1481_; lean_object* v_failures_1555_; lean_object* v_numJobs_1556_; uint8_t v___y_1558_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_failures_1555_ = lean_ctor_get(v_result_1477_, 0);
lean_inc_ref(v_failures_1555_);
v_numJobs_1556_ = lean_ctor_get(v_result_1477_, 1);
lean_inc(v_numJobs_1556_);
lean_dec_ref(v_result_1477_);
v___x_1591_ = lean_array_get_size(v_failures_1555_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = lean_nat_dec_eq(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v_flush_1594_; lean_object* v_putStr_1595_; lean_object* v___y_1601_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec(v_numJobs_1556_);
v_flush_1594_ = lean_ctor_get(v_out_1476_, 0);
lean_inc_ref(v_flush_1594_);
v_putStr_1595_ = lean_ctor_get(v_out_1476_, 4);
v___x_1612_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1595_);
v___x_1613_ = lean_apply_2(v_putStr_1595_, v___x_1612_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec_ref_known(v___x_1613_, 1);
goto v___jp_1602_;
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1616_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1617_ = lean_unsigned_to_nat(78u);
v___x_1618_ = lean_unsigned_to_nat(4u);
v___x_1619_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1620_ = lean_io_error_to_string(v_a_1614_);
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
v___x_1624_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
v___x_1626_ = l_mkPanicMessageWithDecl(v___x_1615_, v___x_1616_, v___x_1617_, v___x_1618_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1626_);
goto v___jp_1602_;
}
v___jp_1596_:
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_apply_1(v_flush_1594_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
return v_a_1598_;
}
else
{
lean_object* v___x_1599_; 
lean_dec_ref_known(v___x_1597_, 1);
v___x_1599_ = lean_box(0);
return v___x_1599_;
}
}
v___jp_1600_:
{
goto v___jp_1596_;
}
v___jp_1602_:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_nat_dec_lt(v___x_1592_, v___x_1591_);
if (v___x_1603_ == 0)
{
lean_dec_ref(v_failures_1555_);
lean_dec_ref(v_out_1476_);
goto v___jp_1596_;
}
else
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_nat_dec_le(v___x_1591_, v___x_1591_);
if (v___x_1605_ == 0)
{
if (v___x_1603_ == 0)
{
lean_dec_ref(v_failures_1555_);
lean_dec_ref(v_out_1476_);
goto v___jp_1596_;
}
else
{
size_t v___x_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = lean_usize_of_nat(v___x_1591_);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1476_, v_failures_1555_, v___x_1606_, v___x_1607_, v___x_1604_);
lean_dec_ref(v_failures_1555_);
v___y_1601_ = v___x_1608_;
goto v___jp_1600_;
}
}
else
{
size_t v___x_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = lean_usize_of_nat(v___x_1591_);
v___x_1611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1476_, v_failures_1555_, v___x_1609_, v___x_1610_, v___x_1604_);
lean_dec_ref(v_failures_1555_);
v___y_1601_ = v___x_1611_;
goto v___jp_1600_;
}
}
}
}
else
{
uint8_t v___x_1628_; 
lean_dec_ref(v_failures_1555_);
v___x_1628_ = l_Lake_BuildConfig_showProgress(v_cfg_1475_);
if (v___x_1628_ == 0)
{
v___y_1558_ = v___x_1628_;
goto v___jp_1557_;
}
else
{
uint8_t v_showSuccess_1629_; 
v_showSuccess_1629_ = lean_ctor_get_uint8(v_cfg_1475_, sizeof(void*)*4 + 4);
v___y_1558_ = v_showSuccess_1629_;
goto v___jp_1557_;
}
}
v___jp_1479_:
{
uint8_t v_noBuild_1482_; 
v_noBuild_1482_ = lean_ctor_get_uint8(v_cfg_1475_, sizeof(void*)*4 + 2);
if (v_noBuild_1482_ == 0)
{
lean_object* v_putStr_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_putStr_1483_ = lean_ctor_get(v_out_1476_, 4);
lean_inc_ref(v_putStr_1483_);
lean_dec_ref(v_out_1476_);
v___x_1484_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1485_ = lean_string_append(v___x_1484_, v___y_1481_);
lean_dec_ref(v___y_1481_);
v___x_1486_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1487_ = lean_string_append(v___x_1485_, v___x_1486_);
lean_inc_ref(v___x_1487_);
v___x_1488_ = lean_apply_2(v_putStr_1483_, v___x_1487_, lean_box(0));
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; 
lean_dec_ref(v___x_1487_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
return v_a_1489_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1518_; 
v_a_1490_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1492_ = v___x_1488_;
v_isShared_1493_ = v_isSharedCheck_1518_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1518_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1494_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1495_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1496_ = lean_unsigned_to_nat(78u);
v___x_1497_ = lean_unsigned_to_nat(4u);
v___x_1498_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1500_, v___y_1480_);
v___x_1502_ = lean_string_append(v___x_1498_, v___x_1501_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
v___x_1505_ = lean_io_error_to_string(v_a_1490_);
v___x_1506_ = lean_string_append(v___x_1504_, v___x_1505_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1508_ = lean_string_append(v___x_1506_, v___x_1507_);
v___x_1509_ = l_String_quote(v___x_1487_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 3);
lean_ctor_set(v___x_1492_, 0, v___x_1509_);
v___x_1511_ = v___x_1492_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1512_ = l_Std_Format_defWidth;
v___x_1513_ = l_Std_Format_pretty(v___x_1511_, v___x_1512_, v___x_1499_, v___x_1499_);
v___x_1514_ = lean_string_append(v___x_1508_, v___x_1513_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = l_mkPanicMessageWithDecl(v___x_1494_, v___x_1495_, v___x_1496_, v___x_1497_, v___x_1514_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1515_);
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_putStr_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_putStr_1519_ = lean_ctor_get(v_out_1476_, 4);
lean_inc_ref(v_putStr_1519_);
lean_dec_ref(v_out_1476_);
v___x_1520_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1521_ = lean_string_append(v___x_1520_, v___y_1481_);
lean_dec_ref(v___y_1481_);
v___x_1522_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1523_ = lean_string_append(v___x_1521_, v___x_1522_);
lean_inc_ref(v___x_1523_);
v___x_1524_ = lean_apply_2(v_putStr_1519_, v___x_1523_, lean_box(0));
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; 
lean_dec_ref(v___x_1523_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
return v_a_1525_;
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1554_; 
v_a_1526_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1528_ = v___x_1524_;
v_isShared_1529_ = v_isSharedCheck_1554_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1524_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1554_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1530_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1532_ = lean_unsigned_to_nat(78u);
v___x_1533_ = lean_unsigned_to_nat(4u);
v___x_1534_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1537_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1536_, v_noBuild_1482_);
v___x_1538_ = lean_string_append(v___x_1534_, v___x_1537_);
lean_dec_ref(v___x_1537_);
v___x_1539_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1540_ = lean_string_append(v___x_1538_, v___x_1539_);
v___x_1541_ = lean_io_error_to_string(v_a_1526_);
v___x_1542_ = lean_string_append(v___x_1540_, v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1544_ = lean_string_append(v___x_1542_, v___x_1543_);
v___x_1545_ = l_String_quote(v___x_1523_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 3);
lean_ctor_set(v___x_1528_, 0, v___x_1545_);
v___x_1547_ = v___x_1528_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1548_ = l_Std_Format_defWidth;
v___x_1549_ = l_Std_Format_pretty(v___x_1547_, v___x_1548_, v___x_1535_, v___x_1535_);
v___x_1550_ = lean_string_append(v___x_1544_, v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_mkPanicMessageWithDecl(v___x_1530_, v___x_1531_, v___x_1532_, v___x_1533_, v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1551_);
return v___x_1552_;
}
}
}
}
}
v___jp_1557_:
{
if (v___y_1558_ == 0)
{
lean_object* v___x_1559_; 
lean_dec(v_numJobs_1556_);
lean_dec_ref(v_out_1476_);
v___x_1559_ = lean_box(0);
return v___x_1559_;
}
else
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_nat_dec_eq(v_numJobs_1556_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_dec_eq(v_numJobs_1556_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = l_Nat_reprFast(v_numJobs_1556_);
v___x_1565_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1566_ = lean_string_append(v___x_1564_, v___x_1565_);
v___y_1480_ = v___y_1558_;
v___y_1481_ = v___x_1566_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1567_; 
lean_dec(v_numJobs_1556_);
v___x_1567_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1480_ = v___y_1558_;
v___y_1481_ = v___x_1567_;
goto v___jp_1479_;
}
}
else
{
lean_object* v_putStr_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec(v_numJobs_1556_);
v_putStr_1568_ = lean_ctor_get(v_out_1476_, 4);
lean_inc_ref(v_putStr_1568_);
lean_dec_ref(v_out_1476_);
v___x_1569_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1570_ = lean_apply_2(v_putStr_1568_, v___x_1569_, lean_box(0));
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
return v_a_1571_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1572_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1573_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1574_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1575_ = lean_unsigned_to_nat(78u);
v___x_1576_ = lean_unsigned_to_nat(4u);
v___x_1577_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1578_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1579_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1578_, v___x_1561_);
v___x_1580_ = lean_string_append(v___x_1577_, v___x_1579_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1582_ = lean_string_append(v___x_1580_, v___x_1581_);
v___x_1583_ = lean_io_error_to_string(v_a_1572_);
v___x_1584_ = lean_string_append(v___x_1582_, v___x_1583_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1588_ = lean_string_append(v___x_1586_, v___x_1587_);
v___x_1589_ = l_mkPanicMessageWithDecl(v___x_1573_, v___x_1574_, v___x_1575_, v___x_1576_, v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1589_);
return v___x_1590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1630_, lean_object* v_out_1631_, lean_object* v_result_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1630_, v_out_1631_, v_result_1632_);
lean_dec_ref(v_cfg_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1635_){
_start:
{
lean_object* v_toMonitorResult_1636_; 
v_toMonitorResult_1636_ = lean_ctor_get(v_self_1635_, 0);
lean_inc_ref(v_toMonitorResult_1636_);
return v_toMonitorResult_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1637_);
lean_dec_ref(v_self_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1640_){
_start:
{
lean_object* v___f_1641_; 
v___f_1641_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1641_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1642_){
_start:
{
lean_object* v_out_1643_; 
v_out_1643_ = lean_ctor_get(v_self_1642_, 1);
if (lean_obj_tag(v_out_1643_) == 0)
{
uint8_t v___x_1644_; 
v___x_1644_ = 0;
return v___x_1644_;
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = 1;
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1646_){
_start:
{
uint8_t v_res_1647_; lean_object* v_r_1648_; 
v_res_1647_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1646_);
lean_dec_ref(v_self_1646_);
v_r_1648_ = lean_box(v_res_1647_);
return v_r_1648_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1649_, lean_object* v_self_1650_){
_start:
{
lean_object* v_out_1651_; 
v_out_1651_ = lean_ctor_get(v_self_1650_, 1);
if (lean_obj_tag(v_out_1651_) == 0)
{
uint8_t v___x_1652_; 
v___x_1652_ = 0;
return v___x_1652_;
}
else
{
uint8_t v___x_1653_; 
v___x_1653_ = 1;
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1654_, lean_object* v_self_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1654_, v_self_1655_);
lean_dec_ref(v_self_1655_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1666_, lean_object* v_job_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_failures_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
lean_inc_ref(v_job_1667_);
v___x_1669_ = l_Lake_Job_toOpaque___redArg(v_job_1667_);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_mk_empty_array_with_capacity(v___x_1670_);
v___x_1672_ = lean_array_push(v___x_1671_, v___x_1669_);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1675_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1676_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1666_, v___x_1672_, v___x_1674_, v___x_1675_);
v_failures_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc_ref(v_failures_1677_);
v___x_1678_ = lean_array_get_size(v_failures_1677_);
lean_dec_ref(v_failures_1677_);
v___x_1679_ = lean_nat_dec_eq(v___x_1678_, v___x_1673_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v_job_1667_);
v___x_1680_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1676_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
return v___x_1681_;
}
else
{
lean_object* v_task_1682_; lean_object* v___x_1683_; 
v_task_1682_ = lean_ctor_get(v_job_1667_, 0);
lean_inc_ref(v_task_1682_);
lean_dec_ref(v_job_1667_);
v___x_1683_ = lean_io_wait(v_task_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1683_, 1);
lean_dec(v_unused_1693_);
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_a_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1688_);
lean_ctor_set(v___x_1686_, 0, v___x_1676_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1702_ = lean_ctor_get(v___x_1683_, 1);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v___x_1683_, 0);
lean_dec(v_unused_1703_);
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v___x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
lean_ctor_set(v___x_1695_, 1, v___x_1697_);
lean_ctor_set(v___x_1695_, 0, v___x_1676_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1704_, lean_object* v_job_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1704_, v_job_1705_);
lean_dec_ref(v_ctx_1704_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1708_, lean_object* v_ctx_1709_, lean_object* v_job_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1709_, v_job_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_ctx_1714_, lean_object* v_job_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1713_, v_ctx_1714_, v_job_1715_);
lean_dec_ref(v_ctx_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(lean_object* v_info_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lake_computeTextFileHash(v_info_1720_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = lean_io_metadata(v_info_1720_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1736_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1736_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1736_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_modified_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint64_t v___x_1732_; lean_object* v___x_1734_; 
v_modified_1729_ = lean_ctor_get(v_a_1725_, 1);
lean_inc_ref(v_modified_1729_);
lean_dec(v_a_1725_);
v___x_1730_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1731_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1731_, 0, v_info_1720_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
lean_ctor_set(v___x_1731_, 2, v_modified_1729_);
v___x_1732_ = lean_unbox_uint64(v_a_1723_);
lean_dec(v_a_1723_);
lean_ctor_set_uint64(v___x_1731_, sizeof(void*)*3, v___x_1732_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1731_);
v___x_1734_ = v___x_1727_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1731_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_a_1723_);
lean_dec_ref(v_info_1720_);
v_a_1737_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1724_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1724_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_info_1720_);
v_a_1745_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1722_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1722_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___boxed(lean_object* v_info_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v_info_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(lean_object* v___x_1759_, lean_object* v_as_1760_, size_t v_sz_1761_, size_t v_i_1762_, lean_object* v_b_1763_){
_start:
{
lean_object* v_a_1766_; uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1762_, v_sz_1761_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v___x_1759_);
return v_b_1763_;
}
else
{
lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1794_; 
v_snd_1771_ = lean_ctor_get(v_b_1763_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_b_1763_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_b_1763_, 0);
lean_dec(v_unused_1795_);
v___x_1773_ = v_b_1763_;
v_isShared_1774_ = v_isSharedCheck_1794_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_dec(v_b_1763_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1794_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1775_ = lean_box(0);
v_a_1776_ = lean_array_uget_borrowed(v_as_1760_, v_i_1762_);
v___x_1777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__0));
lean_inc_ref(v___x_1759_);
v___x_1778_ = l_Lake_joinRelative(v___x_1759_, v___x_1777_);
lean_inc(v_a_1776_);
v___x_1779_ = l_Lake_joinRelative(v___x_1778_, v_a_1776_);
v___x_1780_ = l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0(v___x_1779_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = l_Lake_BuildTrace_mix(v_snd_1771_, v_a_1781_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1782_);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v_a_1766_ = v___x_1784_;
goto v___jp_1765_;
}
}
else
{
lean_object* v_a_1786_; 
v_a_1786_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1780_, 1);
if (lean_obj_tag(v_a_1786_) == 11)
{
lean_object* v___x_1788_; 
lean_dec_ref_known(v_a_1786_, 2);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1788_ = v___x_1773_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_snd_1771_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
v_a_1766_ = v___x_1788_;
goto v___jp_1765_;
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_dec(v_a_1786_);
lean_dec_ref(v___x_1759_);
v___x_1790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___closed__1));
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1790_);
v___x_1792_ = v___x_1773_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_snd_1771_);
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
}
v___jp_1765_:
{
size_t v___x_1767_; size_t v___x_1768_; 
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1762_, v___x_1767_);
v_i_1762_ = v___x_1768_;
v_b_1763_ = v_a_1766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1___boxed(lean_object* v___x_1796_, lean_object* v_as_1797_, lean_object* v_sz_1798_, lean_object* v_i_1799_, lean_object* v_b_1800_, lean_object* v___y_1801_){
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1798_);
lean_dec(v_sz_1798_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1799_);
lean_dec(v_i_1799_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1796_, v_as_1797_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1800_);
lean_dec_ref(v_as_1797_);
return v_res_1804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__1));
v___x_1808_ = l_Lake_BuildTrace_nil(v___x_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__2);
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1823_);
return v___x_1825_;
}
}
static size_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1826_; size_t v_sz_1827_; 
v___x_1826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v_sz_1827_ = lean_array_size(v___x_1826_);
return v_sz_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(size_t v_sz_1828_, size_t v_i_1829_, lean_object* v_bs_1830_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_usize_dec_lt(v_i_1829_, v_sz_1828_);
if (v___x_1832_ == 0)
{
return v_bs_1830_;
}
else
{
lean_object* v_v_1833_; lean_object* v_config_1834_; lean_object* v_dir_1835_; uint8_t v_bootstrap_1836_; lean_object* v_buildDir_1837_; lean_object* v___x_1838_; lean_object* v_bs_x27_1839_; lean_object* v_val_1841_; 
v_v_1833_ = lean_array_uget_borrowed(v_bs_1830_, v_i_1829_);
v_config_1834_ = lean_ctor_get(v_v_1833_, 6);
v_dir_1835_ = lean_ctor_get(v_v_1833_, 4);
lean_inc_ref(v_dir_1835_);
v_bootstrap_1836_ = lean_ctor_get_uint8(v_config_1834_, sizeof(void*)*28);
v_buildDir_1837_ = lean_ctor_get(v_config_1834_, 5);
lean_inc_ref(v_buildDir_1837_);
v___x_1838_ = lean_unsigned_to_nat(0u);
v_bs_x27_1839_ = lean_array_uset(v_bs_1830_, v_i_1829_, v___x_1838_);
if (v_bootstrap_1836_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v_buildDir_1837_);
lean_dec_ref(v_dir_1835_);
v___x_1846_ = lean_box(0);
v_val_1841_ = v___x_1846_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; size_t v_sz_1853_; size_t v___x_1854_; lean_object* v___x_1855_; lean_object* v_fst_1856_; 
v___x_1847_ = l_System_FilePath_normalize(v_buildDir_1837_);
v___x_1848_ = l_Lake_joinRelative(v_dir_1835_, v___x_1847_);
v___x_1849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__0));
v___x_1850_ = l_Lake_joinRelative(v___x_1848_, v___x_1849_);
v___x_1851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__7));
v___x_1852_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__8);
v_sz_1853_ = lean_usize_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___closed__9);
v___x_1854_ = ((size_t)0ULL);
lean_inc_ref(v___x_1850_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__1(v___x_1850_, v___x_1851_, v_sz_1853_, v___x_1854_, v___x_1852_);
v_fst_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_fst_1856_);
if (lean_obj_tag(v_fst_1856_) == 0)
{
lean_object* v_snd_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_snd_1857_ = lean_ctor_get(v___x_1855_, 1);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1855_, 0);
lean_dec(v_unused_1866_);
v___x_1859_ = v___x_1855_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_snd_1857_);
lean_dec(v___x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1850_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_snd_1857_);
v___x_1862_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
v_val_1841_ = v___x_1863_;
goto v___jp_1840_;
}
}
}
else
{
lean_object* v_val_1867_; 
lean_dec_ref(v___x_1855_);
lean_dec_ref(v___x_1850_);
v_val_1867_ = lean_ctor_get(v_fst_1856_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v_fst_1856_, 1);
v_val_1841_ = v_val_1867_;
goto v___jp_1840_;
}
}
v___jp_1840_:
{
size_t v___x_1842_; size_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_add(v_i_1829_, v___x_1842_);
v___x_1844_ = lean_array_uset(v_bs_x27_1839_, v_i_1829_, v_val_1841_);
v_i_1829_ = v___x_1843_;
v_bs_1830_ = v___x_1844_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2___boxed(lean_object* v_sz_1868_, lean_object* v_i_1869_, lean_object* v_bs_1870_, lean_object* v___y_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1868_);
lean_dec(v_sz_1868_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1869_);
lean_dec(v_i_1869_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_boxed_1872_, v_i_boxed_1873_, v_bs_1870_);
return v_res_1874_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_versionStringCore;
v___x_1877_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__0));
v___x_1878_ = lean_string_append(v___x_1877_, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__2));
v___x_1881_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__1);
v___x_1882_ = lean_string_append(v___x_1881_, v___x_1880_);
return v___x_1882_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_nat_to_int(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5(void){
_start:
{
uint32_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = 0;
v___x_1886_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__4);
v___x_1887_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set_uint32(v___x_1887_, sizeof(void*)*1, v___x_1885_);
return v___x_1887_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_unsigned_to_nat(16u);
v___x_1890_ = lean_mk_array(v___x_1889_, v___x_1888_);
return v___x_1890_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__6);
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext(lean_object* v_ws_1896_, lean_object* v_cfg_1897_, lean_object* v_jobs_1898_){
_start:
{
lean_object* v___y_1901_; uint8_t v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1905_; uint8_t v___y_1906_; uint8_t v___y_1907_; lean_object* v___y_1908_; uint8_t v___y_1909_; lean_object* v_val_1910_; lean_object* v_val_1928_; uint8_t v___x_1948_; 
v___x_1948_ = l_System_Platform_isOSX;
if (v___x_1948_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_1949_; 
v_macosxDeploymentTarget_x3f_1949_ = lean_ctor_get(v_cfg_1897_, 3);
lean_inc(v_macosxDeploymentTarget_x3f_1949_);
v_val_1928_ = v_macosxDeploymentTarget_x3f_1949_;
goto v___jp_1927_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_1950_; 
v_macosxDeploymentTarget_x3f_1950_ = lean_ctor_get(v_cfg_1897_, 3);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_1950_) == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___y_1954_; 
v___x_1951_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__8));
v___x_1952_ = lean_io_getenv(v___x_1951_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1956_; 
v___x_1956_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__9));
v___y_1954_ = v___x_1956_;
goto v___jp_1953_;
}
else
{
lean_object* v_val_1957_; 
v_val_1957_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v___x_1952_, 1);
v___y_1954_ = v_val_1957_;
goto v___jp_1953_;
}
v___jp_1953_:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___y_1954_);
v_val_1928_ = v___x_1955_;
goto v___jp_1927_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_1950_);
v_val_1928_ = v_macosxDeploymentTarget_x3f_1950_;
goto v___jp_1927_;
}
}
v___jp_1900_:
{
lean_object* v_lakeEnv_1911_; lean_object* v_packages_1912_; size_t v_sz_1913_; size_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_lakeEnv_1911_ = lean_ctor_get(v_ws_1896_, 0);
v_packages_1912_ = lean_ctor_get(v_ws_1896_, 4);
v_sz_1913_ = lean_array_size(v_packages_1912_);
v___x_1914_ = ((size_t)0ULL);
lean_inc_ref(v_packages_1912_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__2(v_sz_1913_, v___x_1914_, v_packages_1912_);
v___x_1916_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v___x_1916_, 0, v___y_1903_);
lean_ctor_set(v___x_1916_, 1, v___y_1908_);
lean_ctor_set(v___x_1916_, 2, v___y_1901_);
lean_ctor_set(v___x_1916_, 3, v___y_1904_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*4, v___y_1906_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*4 + 1, v___y_1902_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*4 + 2, v___y_1909_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*4 + 3, v___y_1907_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*4 + 4, v___y_1905_);
v___x_1917_ = l_Lake_Env_leanGithash(v_lakeEnv_1911_);
v___x_1918_ = l_Lake_Hash_nil;
v___x_1919_ = lean_string_hash(v___x_1917_);
v___x_1920_ = lean_uint64_mix_hash(v___x_1918_, v___x_1919_);
v___x_1921_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__3);
v___x_1922_ = lean_string_append(v___x_1921_, v___x_1917_);
lean_dec_ref(v___x_1917_);
v___x_1923_ = ((lean_object*)(l_Lake_BuildTrace_compute___at___00__private_Lake_Build_Run_0__Lake_mkBuildContext_spec__0___closed__0));
v___x_1924_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__5);
v___x_1925_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1925_, 0, v___x_1922_);
lean_ctor_set(v___x_1925_, 1, v___x_1923_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
lean_ctor_set_uint64(v___x_1925_, sizeof(void*)*3, v___x_1920_);
v___x_1926_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1916_);
lean_ctor_set(v___x_1926_, 1, v_ws_1896_);
lean_ctor_set(v___x_1926_, 2, v___x_1925_);
lean_ctor_set(v___x_1926_, 3, v___x_1915_);
lean_ctor_set(v___x_1926_, 4, v_jobs_1898_);
lean_ctor_set(v___x_1926_, 5, v_val_1910_);
return v___x_1926_;
}
v___jp_1927_:
{
lean_object* v_outputsFile_x3f_1929_; 
v_outputsFile_x3f_1929_ = lean_ctor_get(v_cfg_1897_, 1);
lean_inc(v_outputsFile_x3f_1929_);
if (lean_obj_tag(v_outputsFile_x3f_1929_) == 0)
{
lean_object* v_toLogConfig_1930_; uint8_t v_oldMode_1931_; uint8_t v_trustHash_1932_; uint8_t v_noBuild_1933_; uint8_t v_verbosity_1934_; uint8_t v_showSuccess_1935_; lean_object* v_leanOptOverrides_1936_; lean_object* v___x_1937_; 
v_toLogConfig_1930_ = lean_ctor_get(v_cfg_1897_, 0);
lean_inc_ref(v_toLogConfig_1930_);
v_oldMode_1931_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4);
v_trustHash_1932_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 1);
v_noBuild_1933_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 2);
v_verbosity_1934_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 3);
v_showSuccess_1935_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 4);
v_leanOptOverrides_1936_ = lean_ctor_get(v_cfg_1897_, 2);
lean_inc(v_leanOptOverrides_1936_);
lean_dec_ref(v_cfg_1897_);
v___x_1937_ = lean_box(0);
v___y_1901_ = v_leanOptOverrides_1936_;
v___y_1902_ = v_trustHash_1932_;
v___y_1903_ = v_toLogConfig_1930_;
v___y_1904_ = v_val_1928_;
v___y_1905_ = v_showSuccess_1935_;
v___y_1906_ = v_oldMode_1931_;
v___y_1907_ = v_verbosity_1934_;
v___y_1908_ = v_outputsFile_x3f_1929_;
v___y_1909_ = v_noBuild_1933_;
v_val_1910_ = v___x_1937_;
goto v___jp_1900_;
}
else
{
lean_object* v_toLogConfig_1938_; uint8_t v_oldMode_1939_; uint8_t v_trustHash_1940_; uint8_t v_noBuild_1941_; uint8_t v_verbosity_1942_; uint8_t v_showSuccess_1943_; lean_object* v_leanOptOverrides_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_toLogConfig_1938_ = lean_ctor_get(v_cfg_1897_, 0);
lean_inc_ref(v_toLogConfig_1938_);
v_oldMode_1939_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4);
v_trustHash_1940_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 1);
v_noBuild_1941_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 2);
v_verbosity_1942_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 3);
v_showSuccess_1943_ = lean_ctor_get_uint8(v_cfg_1897_, sizeof(void*)*4 + 4);
v_leanOptOverrides_1944_ = lean_ctor_get(v_cfg_1897_, 2);
lean_inc(v_leanOptOverrides_1944_);
lean_dec_ref(v_cfg_1897_);
v___x_1945_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7, &l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext___closed__7);
v___x_1946_ = lean_st_mk_ref(v___x_1945_);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
v___y_1901_ = v_leanOptOverrides_1944_;
v___y_1902_ = v_trustHash_1940_;
v___y_1903_ = v_toLogConfig_1938_;
v___y_1904_ = v_val_1928_;
v___y_1905_ = v_showSuccess_1943_;
v___y_1906_ = v_oldMode_1939_;
v___y_1907_ = v_verbosity_1942_;
v___y_1908_ = v_outputsFile_x3f_1929_;
v___y_1909_ = v_noBuild_1941_;
v_val_1910_ = v___x_1947_;
goto v___jp_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext___boxed(lean_object* v_ws_1958_, lean_object* v_cfg_1959_, lean_object* v_jobs_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_1958_, v_cfg_1959_, v_jobs_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_log_1971_; uint8_t v_action_1972_; uint8_t v_wantsRebuild_1973_; lean_object* v_trace_1974_; lean_object* v_buildTime_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2004_; 
v_log_1971_ = lean_ctor_get(v___y_1969_, 0);
v_action_1972_ = lean_ctor_get_uint8(v___y_1969_, sizeof(void*)*3);
v_wantsRebuild_1973_ = lean_ctor_get_uint8(v___y_1969_, sizeof(void*)*3 + 1);
v_trace_1974_ = lean_ctor_get(v___y_1969_, 1);
v_buildTime_1975_ = lean_ctor_get(v___y_1969_, 2);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___y_1969_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1977_ = v___y_1969_;
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_buildTime_1975_);
lean_inc(v_trace_1974_);
lean_inc(v_log_1971_);
lean_dec(v___y_1969_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_apply_7(v_build_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v_log_1971_, lean_box(0));
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1991_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_a_1981_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1983_ = v___x_1979_;
v_isShared_1984_ = v_isSharedCheck_1991_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1991_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_a_1981_);
v___x_1986_ = v___x_1977_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1981_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_trace_1974_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_buildTime_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*3, v_action_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*3 + 1, v_wantsRebuild_1973_);
v___x_1986_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v___x_1986_);
v___x_1988_ = v___x_1983_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1980_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2003_; 
v_a_1992_ = lean_ctor_get(v___x_1979_, 0);
v_a_1993_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1995_ = v___x_1979_;
v_isShared_1996_ = v_isSharedCheck_2003_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_inc(v_a_1992_);
lean_dec(v___x_1979_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2003_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_a_1993_);
v___x_1998_ = v___x_1977_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1993_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_trace_1974_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_buildTime_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*3, v_action_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_2002_, sizeof(void*)*3 + 1, v_wantsRebuild_1973_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_2000_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___x_1998_);
v___x_2000_ = v___x_1995_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1992_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_2015_, lean_object* v_build_2016_, lean_object* v_caption_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2019_ = lean_box(1);
v___x_2020_ = lean_st_mk_ref(v___x_2019_);
v___f_2021_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2021_, 0, v_build_2016_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_box(0);
v___x_2026_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_2027_ = l_Lake_Job_async___redArg(v___x_2022_, v___f_2021_, v___x_2023_, v_caption_2017_, v___x_2026_, v___x_2025_, v___x_2024_, v___x_2020_, v_bctx_2015_);
v___x_2028_ = lean_st_ref_get(v___x_2020_);
lean_dec(v___x_2020_);
lean_dec(v___x_2028_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_2029_, lean_object* v_build_2030_, lean_object* v_caption_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2029_, v_build_2030_, v_caption_2031_);
lean_dec_ref(v_bctx_2029_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_2034_, lean_object* v_bctx_2035_, lean_object* v_build_2036_, lean_object* v_caption_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_2035_, v_build_2036_, v_caption_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_bctx_2041_, lean_object* v_build_2042_, lean_object* v_caption_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_2040_, v_bctx_2041_, v_build_2042_, v_caption_2043_);
lean_dec_ref(v_bctx_2041_);
return v_res_2045_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v_x_2046_, lean_object* v_x_2047_){
_start:
{
if (lean_obj_tag(v_x_2046_) == 0)
{
if (lean_obj_tag(v_x_2047_) == 0)
{
uint8_t v___x_2048_; 
v___x_2048_ = 1;
return v___x_2048_;
}
else
{
uint8_t v___x_2049_; 
v___x_2049_ = 0;
return v___x_2049_;
}
}
else
{
if (lean_obj_tag(v_x_2047_) == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = 0;
return v___x_2050_;
}
else
{
lean_object* v_val_2051_; uint8_t v___x_2052_; 
v_val_2051_ = lean_ctor_get(v_x_2047_, 0);
v___x_2052_ = lean_unbox(v_val_2051_);
if (v___x_2052_ == 0)
{
lean_object* v_val_2053_; uint8_t v___x_2054_; 
v_val_2053_ = lean_ctor_get(v_x_2046_, 0);
v___x_2054_ = lean_unbox(v_val_2053_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = 1;
return v___x_2055_;
}
else
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_unbox(v_val_2051_);
return v___x_2056_;
}
}
else
{
lean_object* v_val_2057_; uint8_t v___x_2058_; 
v_val_2057_ = lean_ctor_get(v_x_2046_, 0);
v___x_2058_ = lean_unbox(v_val_2057_);
return v___x_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v_x_2059_, lean_object* v_x_2060_){
_start:
{
uint8_t v_res_2061_; lean_object* v_r_2062_; 
v_res_2061_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_2059_, v_x_2060_);
lean_dec(v_x_2060_);
lean_dec(v_x_2059_);
v_r_2062_ = lean_box(v_res_2061_);
return v_r_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_2063_, uint8_t v___x_2064_, uint8_t v___x_2065_, lean_object* v_as_2066_, size_t v_i_2067_, size_t v_stop_2068_, lean_object* v_b_2069_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_usize_dec_eq(v_i_2067_, v_stop_2068_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; 
v___x_2072_ = lean_array_uget_borrowed(v_as_2066_, v_i_2067_);
lean_inc_ref(v___x_2063_);
v___x_2073_ = l_Lake_logToStream(v___x_2072_, v___x_2063_, v___x_2064_, v___x_2065_);
v___x_2074_ = ((size_t)1ULL);
v___x_2075_ = lean_usize_add(v_i_2067_, v___x_2074_);
v_i_2067_ = v___x_2075_;
v_b_2069_ = v___x_2073_;
goto _start;
}
else
{
lean_dec_ref(v___x_2063_);
return v_b_2069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, lean_object* v_as_2080_, lean_object* v_i_2081_, lean_object* v_stop_2082_, lean_object* v_b_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v___x_1007__boxed_2085_; uint8_t v___x_1008__boxed_2086_; size_t v_i_boxed_2087_; size_t v_stop_boxed_2088_; lean_object* v_res_2089_; 
v___x_1007__boxed_2085_ = lean_unbox(v___x_2078_);
v___x_1008__boxed_2086_ = lean_unbox(v___x_2079_);
v_i_boxed_2087_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_stop_boxed_2088_ = lean_unbox_usize(v_stop_2082_);
lean_dec(v_stop_2082_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2077_, v___x_1007__boxed_2085_, v___x_1008__boxed_2086_, v_as_2080_, v_i_boxed_2087_, v_stop_boxed_2088_, v_b_2083_);
lean_dec_ref(v_as_2080_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_2090_, uint8_t v___x_2091_, uint8_t v___x_2092_, lean_object* v_ws_2093_, lean_object* v_outputsRef_x3f_2094_, lean_object* v_out_2095_, lean_object* v_outputsFile_2096_, uint8_t v_isVerbose_2097_){
_start:
{
lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2111_; lean_object* v___y_2112_; uint8_t v___x_2194_; 
v___x_2194_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_2093_);
if (v___x_2194_ == 0)
{
lean_object* v_packages_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_baseName_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_packages_2195_ = lean_ctor_get(v_ws_2093_, 4);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_array_fget_borrowed(v_packages_2195_, v___x_2196_);
v_baseName_2198_ = lean_ctor_get(v___x_2197_, 1);
lean_inc(v_baseName_2198_);
v___x_2199_ = l_Lean_Name_toString(v_baseName_2198_, v___x_2194_);
v___x_2200_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16));
v___x_2201_ = lean_string_append(v___x_2199_, v___x_2200_);
v___x_2202_ = 2;
v___x_2203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*1, v___x_2202_);
lean_inc_ref(v___x_2090_);
v___x_2204_ = l_Lake_logToStream(v___x_2203_, v___x_2090_, v___x_2091_, v___x_2092_);
lean_dec_ref_known(v___x_2203_, 1);
goto v___jp_2120_;
}
else
{
goto v___jp_2120_;
}
v___jp_2099_:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_box(0);
return v___x_2100_;
}
v___jp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = lean_array_get_size(v___y_2102_);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_nat_dec_lt(v___y_2103_, v___x_2104_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___y_2102_);
lean_dec_ref(v___x_2090_);
return v___x_2105_;
}
else
{
size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2104_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2090_, v___x_2091_, v___x_2092_, v___y_2102_, v___x_2107_, v___x_2108_, v___x_2105_);
lean_dec_ref(v___y_2102_);
return v___x_2109_;
}
}
v___jp_2110_:
{
if (v_isVerbose_2097_ == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___x_2090_);
v___x_2113_ = lean_box(0);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2114_ = lean_array_get_size(v___y_2111_);
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_nat_dec_lt(v___y_2112_, v___x_2114_);
if (v___x_2116_ == 0)
{
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___x_2090_);
return v___x_2115_;
}
else
{
size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = lean_usize_of_nat(v___x_2114_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_2090_, v___x_2091_, v___x_2092_, v___y_2111_, v___x_2117_, v___x_2118_, v___x_2115_);
lean_dec_ref(v___y_2111_);
return v___x_2119_;
}
}
}
v___jp_2120_:
{
if (lean_obj_tag(v_outputsRef_x3f_2094_) == 1)
{
lean_object* v_val_2121_; lean_object* v___x_2122_; lean_object* v_packages_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_config_2126_; lean_object* v_toLeanConfig_2127_; lean_object* v_platformIndependent_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_val_2121_ = lean_ctor_get(v_outputsRef_x3f_2094_, 0);
v___x_2122_ = lean_st_ref_get(v_val_2121_);
v_packages_2123_ = lean_ctor_get(v_ws_2093_, 4);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = lean_array_fget_borrowed(v_packages_2123_, v___x_2124_);
v_config_2126_ = lean_ctor_get(v___x_2125_, 6);
v_toLeanConfig_2127_ = lean_ctor_get(v_config_2126_, 1);
v_platformIndependent_2128_ = lean_ctor_get(v_toLeanConfig_2127_, 10);
v___x_2129_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_2130_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_2128_, v___x_2129_);
v___x_2131_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_2132_ = l_Lake_CacheMap_writeFile(v_outputsFile_2096_, v___x_2122_, v___x_2130_, v___x_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 2);
v___x_2134_ = lean_array_get_size(v_a_2133_);
v___x_2135_ = lean_nat_dec_eq(v___x_2134_, v___x_2124_);
if (v___x_2135_ == 0)
{
if (v_isVerbose_2097_ == 0)
{
lean_dec(v_a_2133_);
lean_dec_ref(v_out_2095_);
lean_dec_ref(v___x_2090_);
goto v___jp_2099_;
}
else
{
lean_object* v_putStr_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_putStr_2136_ = lean_ctor_get(v_out_2095_, 4);
lean_inc_ref(v_putStr_2136_);
lean_dec_ref(v_out_2095_);
v___x_2137_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_2138_ = lean_apply_2(v_putStr_2136_, v___x_2137_, lean_box(0));
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_dec_ref_known(v___x_2138_, 1);
v___y_2102_ = v_a_2133_;
v___y_2103_ = v___x_2124_;
goto v___jp_2101_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2141_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2142_ = lean_unsigned_to_nat(78u);
v___x_2143_ = lean_unsigned_to_nat(4u);
v___x_2144_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2145_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2146_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2145_, v_isVerbose_2097_);
v___x_2147_ = lean_string_append(v___x_2144_, v___x_2146_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2149_ = lean_string_append(v___x_2147_, v___x_2148_);
v___x_2150_ = lean_io_error_to_string(v_a_2139_);
v___x_2151_ = lean_string_append(v___x_2149_, v___x_2150_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
v___x_2154_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_2155_ = lean_string_append(v___x_2153_, v___x_2154_);
v___x_2156_ = l_mkPanicMessageWithDecl(v___x_2140_, v___x_2141_, v___x_2142_, v___x_2143_, v___x_2155_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2156_);
v___y_2102_ = v_a_2133_;
v___y_2103_ = v___x_2124_;
goto v___jp_2101_;
}
}
}
else
{
lean_dec(v_a_2133_);
lean_dec_ref(v_out_2095_);
lean_dec_ref(v___x_2090_);
goto v___jp_2099_;
}
}
else
{
lean_object* v_a_2158_; lean_object* v_putStr_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_a_2158_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2132_, 2);
v_putStr_2159_ = lean_ctor_get(v_out_2095_, 4);
lean_inc_ref(v_putStr_2159_);
lean_dec_ref(v_out_2095_);
v___x_2160_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_2161_ = lean_apply_2(v_putStr_2159_, v___x_2160_, lean_box(0));
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_dec_ref_known(v___x_2161_, 1);
v___y_2111_ = v_a_2158_;
v___y_2112_ = v___x_2124_;
goto v___jp_2110_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2164_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2165_ = lean_unsigned_to_nat(78u);
v___x_2166_ = lean_unsigned_to_nat(4u);
v___x_2167_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2168_ = lean_io_error_to_string(v_a_2162_);
v___x_2169_ = lean_string_append(v___x_2167_, v___x_2168_);
lean_dec_ref(v___x_2168_);
v___x_2170_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2171_ = lean_string_append(v___x_2169_, v___x_2170_);
v___x_2172_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_2173_ = lean_string_append(v___x_2171_, v___x_2172_);
v___x_2174_ = l_mkPanicMessageWithDecl(v___x_2163_, v___x_2164_, v___x_2165_, v___x_2166_, v___x_2173_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2174_);
v___y_2111_ = v_a_2158_;
v___y_2112_ = v___x_2124_;
goto v___jp_2110_;
}
}
}
else
{
lean_object* v_putStr_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v_outputsFile_2096_);
lean_dec_ref(v___x_2090_);
v_putStr_2176_ = lean_ctor_get(v_out_2095_, 4);
lean_inc_ref(v_putStr_2176_);
lean_dec_ref(v_out_2095_);
v___x_2177_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_2178_ = lean_apply_2(v_putStr_2176_, v___x_2177_, lean_box(0));
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
return v_a_2179_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_a_2180_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2181_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2182_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2183_ = lean_unsigned_to_nat(78u);
v___x_2184_ = lean_unsigned_to_nat(4u);
v___x_2185_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2186_ = lean_io_error_to_string(v_a_2180_);
v___x_2187_ = lean_string_append(v___x_2185_, v___x_2186_);
lean_dec_ref(v___x_2186_);
v___x_2188_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2189_ = lean_string_append(v___x_2187_, v___x_2188_);
v___x_2190_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15);
v___x_2191_ = lean_string_append(v___x_2189_, v___x_2190_);
v___x_2192_ = l_mkPanicMessageWithDecl(v___x_2181_, v___x_2182_, v___x_2183_, v___x_2184_, v___x_2191_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2192_);
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2205_, lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v_ws_2208_, lean_object* v_outputsRef_x3f_2209_, lean_object* v_out_2210_, lean_object* v_outputsFile_2211_, lean_object* v_isVerbose_2212_, lean_object* v_a_2213_){
_start:
{
uint8_t v___x_1177__boxed_2214_; uint8_t v___x_1178__boxed_2215_; uint8_t v_isVerbose_boxed_2216_; lean_object* v_res_2217_; 
v___x_1177__boxed_2214_ = lean_unbox(v___x_2206_);
v___x_1178__boxed_2215_ = lean_unbox(v___x_2207_);
v_isVerbose_boxed_2216_ = lean_unbox(v_isVerbose_2212_);
v_res_2217_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2205_, v___x_1177__boxed_2214_, v___x_1178__boxed_2215_, v_ws_2208_, v_outputsRef_x3f_2209_, v_out_2210_, v_outputsFile_2211_, v_isVerbose_boxed_2216_);
lean_dec(v_outputsRef_x3f_2209_);
lean_dec_ref(v_ws_2208_);
return v_res_2217_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = 3;
v___x_2219_ = lean_uint32_to_uint8(v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2220_, lean_object* v_bctx_2221_, lean_object* v_mctx_2222_, lean_object* v_result_2223_){
_start:
{
lean_object* v___y_2226_; lean_object* v_out_2229_; uint8_t v_outLv_2230_; uint8_t v_useAnsi_2231_; lean_object* v_toMonitorResult_2232_; lean_object* v_out_2233_; lean_object* v___x_2234_; uint8_t v_noBuild_2235_; uint8_t v_verbosity_2236_; lean_object* v_outputsFile_x3f_2237_; 
v_out_2229_ = lean_ctor_get(v_mctx_2222_, 1);
lean_inc_ref_n(v_out_2229_, 2);
v_outLv_2230_ = lean_ctor_get_uint8(v_mctx_2222_, sizeof(void*)*3);
v_useAnsi_2231_ = lean_ctor_get_uint8(v_mctx_2222_, sizeof(void*)*3 + 4);
lean_dec_ref(v_mctx_2222_);
v_toMonitorResult_2232_ = lean_ctor_get(v_result_2223_, 0);
lean_inc_ref_n(v_toMonitorResult_2232_, 2);
v_out_2233_ = lean_ctor_get(v_result_2223_, 1);
lean_inc_ref(v_out_2233_);
lean_dec_ref(v_result_2223_);
v___x_2234_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2220_, v_out_2229_, v_toMonitorResult_2232_);
v_noBuild_2235_ = lean_ctor_get_uint8(v_cfg_2220_, sizeof(void*)*4 + 2);
v_verbosity_2236_ = lean_ctor_get_uint8(v_cfg_2220_, sizeof(void*)*4 + 3);
v_outputsFile_x3f_2237_ = lean_ctor_get(v_cfg_2220_, 1);
lean_inc(v_outputsFile_x3f_2237_);
lean_dec_ref(v_cfg_2220_);
if (lean_obj_tag(v_outputsFile_x3f_2237_) == 1)
{
lean_object* v_val_2252_; lean_object* v_toContext_2253_; lean_object* v_outputsRef_x3f_2254_; uint8_t v___y_2256_; 
v_val_2252_ = lean_ctor_get(v_outputsFile_x3f_2237_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v_outputsFile_x3f_2237_, 1);
v_toContext_2253_ = lean_ctor_get(v_bctx_2221_, 1);
v_outputsRef_x3f_2254_ = lean_ctor_get(v_bctx_2221_, 5);
if (v_verbosity_2236_ == 2)
{
uint8_t v___x_2258_; 
v___x_2258_ = 1;
v___y_2256_ = v___x_2258_;
goto v___jp_2255_;
}
else
{
uint8_t v___x_2259_; 
v___x_2259_ = 0;
v___y_2256_ = v___x_2259_;
goto v___jp_2255_;
}
v___jp_2255_:
{
lean_object* v___x_2257_; 
lean_inc_ref(v_out_2229_);
v___x_2257_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2229_, v_outLv_2230_, v_useAnsi_2231_, v_toContext_2253_, v_outputsRef_x3f_2254_, v_out_2229_, v_val_2252_, v___y_2256_);
goto v___jp_2238_;
}
}
else
{
lean_dec(v_outputsFile_x3f_2237_);
lean_dec_ref(v_out_2229_);
goto v___jp_2238_;
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_mk_io_user_error(v___y_2226_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
v___jp_2238_:
{
if (lean_obj_tag(v_out_2233_) == 0)
{
if (v_noBuild_2235_ == 0)
{
lean_object* v_a_2239_; 
lean_dec_ref(v_toMonitorResult_2232_);
v_a_2239_ = lean_ctor_get(v_out_2233_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v_out_2233_, 1);
v___y_2226_ = v_a_2239_;
goto v___jp_2225_;
}
else
{
uint8_t v_wantsRebuild_2240_; 
v_wantsRebuild_2240_ = lean_ctor_get_uint8(v_toMonitorResult_2232_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2232_);
if (v_wantsRebuild_2240_ == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v_out_2233_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v_out_2233_, 1);
v___y_2226_ = v_a_2241_;
goto v___jp_2225_;
}
else
{
uint8_t v___x_2242_; lean_object* v___x_2243_; 
lean_dec_ref_known(v_out_2233_, 1);
v___x_2242_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2243_ = lean_io_exit(v___x_2242_);
return v___x_2243_;
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_toMonitorResult_2232_);
v_a_2244_ = lean_ctor_get(v_out_2233_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_out_2233_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v_out_2233_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v_out_2233_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 0);
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2260_, lean_object* v_bctx_2261_, lean_object* v_mctx_2262_, lean_object* v_result_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2260_, v_bctx_2261_, v_mctx_2262_, v_result_2263_);
lean_dec_ref(v_bctx_2261_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2266_, lean_object* v_cfg_2267_, lean_object* v_bctx_2268_, lean_object* v_mctx_2269_, lean_object* v_result_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2267_, v_bctx_2268_, v_mctx_2269_, v_result_2270_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2273_, lean_object* v_cfg_2274_, lean_object* v_bctx_2275_, lean_object* v_mctx_2276_, lean_object* v_result_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2273_, v_cfg_2274_, v_bctx_2275_, v_mctx_2276_, v_result_2277_);
lean_dec_ref(v_bctx_2275_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2280_, lean_object* v_build_2281_, lean_object* v_cfg_2282_, lean_object* v_caption_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2285_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2286_ = lean_st_mk_ref(v___x_2285_);
lean_inc(v___x_2286_);
v___x_2287_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2282_, v___x_2286_);
lean_inc_ref(v_cfg_2282_);
v___x_2288_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2280_, v_cfg_2282_, v___x_2286_);
v___x_2289_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2288_, v_build_2281_, v_caption_2283_);
v___x_2290_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2287_, v___x_2289_);
v___x_2291_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2282_, v___x_2288_, v___x_2287_, v___x_2290_);
lean_dec_ref(v___x_2288_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2292_, lean_object* v_build_2293_, lean_object* v_cfg_2294_, lean_object* v_caption_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2292_, v_build_2293_, v_cfg_2294_, v_caption_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2298_, lean_object* v_ws_2299_, lean_object* v_build_2300_, lean_object* v_cfg_2301_, lean_object* v_caption_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2299_, v_build_2300_, v_cfg_2301_, v_caption_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_ws_2306_, lean_object* v_build_2307_, lean_object* v_cfg_2308_, lean_object* v_caption_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2305_, v_ws_2306_, v_build_2307_, v_cfg_2308_, v_caption_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2315_, lean_object* v_job_2316_){
_start:
{
lean_object* v___x_2318_; lean_object* v_out_2319_; 
v___x_2318_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2315_, v_job_2316_);
v_out_2319_ = lean_ctor_get(v___x_2318_, 1);
lean_inc_ref(v_out_2319_);
if (lean_obj_tag(v_out_2319_) == 0)
{
lean_object* v_toMonitorResult_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2335_; 
v_toMonitorResult_2320_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v___x_2318_, 1);
lean_dec(v_unused_2336_);
v___x_2322_ = v___x_2318_;
v_isShared_2323_ = v_isSharedCheck_2335_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_toMonitorResult_2320_);
lean_dec(v___x_2318_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2335_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2334_; 
v_a_2324_ = lean_ctor_get(v_out_2319_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_out_2319_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2326_ = v_out_2319_;
v_isShared_2327_ = v_isSharedCheck_2334_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v_out_2319_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2334_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2329_);
v___x_2331_ = v___x_2322_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_toMonitorResult_2320_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2360_; 
v_a_2337_ = lean_ctor_get(v_out_2319_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_out_2319_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2339_ = v_out_2319_;
v_isShared_2340_ = v_isSharedCheck_2360_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v_out_2319_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2360_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_toMonitorResult_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2358_; 
v_toMonitorResult_2341_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2318_, 1);
lean_dec(v_unused_2359_);
v___x_2343_ = v___x_2318_;
v_isShared_2344_ = v_isSharedCheck_2358_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_toMonitorResult_2341_);
lean_dec(v___x_2318_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2358_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_task_2345_; lean_object* v___x_2346_; 
v_task_2345_ = lean_ctor_get(v_a_2337_, 0);
lean_inc_ref(v_task_2345_);
lean_dec(v_a_2337_);
v___x_2346_ = lean_io_wait(v_task_2345_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 2);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v_a_2347_);
v___x_2349_ = v___x_2339_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2349_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v___x_2349_);
v___x_2351_ = v___x_2343_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_toMonitorResult_2341_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec_ref_known(v___x_2346_, 2);
lean_del_object(v___x_2339_);
v___x_2354_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v___x_2354_);
v___x_2356_ = v___x_2343_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_toMonitorResult_2341_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2361_, lean_object* v_job_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2361_, v_job_2362_);
lean_dec_ref(v_mctx_2361_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2365_, lean_object* v_mctx_2366_, lean_object* v_job_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2366_, v_job_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_mctx_2371_, lean_object* v_job_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2370_, v_mctx_2371_, v_job_2372_);
lean_dec_ref(v_mctx_2371_);
return v_res_2374_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2388_, lean_object* v_build_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_out_2401_; 
v___x_2391_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2392_ = lean_st_mk_ref(v___x_2391_);
v___x_2393_ = 0;
v___x_2394_ = 1;
v___x_2395_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2392_);
v___x_2396_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2395_, v___x_2392_);
v___x_2397_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2388_, v___x_2395_, v___x_2392_);
v___x_2398_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2399_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2397_, v_build_2389_, v___x_2398_);
lean_dec_ref(v___x_2397_);
v___x_2400_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2396_, v___x_2399_);
lean_dec_ref(v___x_2396_);
v_out_2401_ = lean_ctor_get(v___x_2400_, 1);
lean_inc_ref(v_out_2401_);
lean_dec_ref(v___x_2400_);
if (lean_obj_tag(v_out_2401_) == 0)
{
lean_dec_ref_known(v_out_2401_, 1);
return v___x_2393_;
}
else
{
lean_dec_ref_known(v_out_2401_, 1);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2402_, lean_object* v_build_2403_, lean_object* v_a_2404_){
_start:
{
uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_res_2405_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2402_, v_build_2403_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2407_, lean_object* v_ws_2408_, lean_object* v_build_2409_){
_start:
{
uint8_t v___x_2411_; 
v___x_2411_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2408_, v_build_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2412_, lean_object* v_ws_2413_, lean_object* v_build_2414_, lean_object* v_a_2415_){
_start:
{
uint8_t v_res_2416_; lean_object* v_r_2417_; 
v_res_2416_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2412_, v_ws_2413_, v_build_2414_);
v_r_2417_ = lean_box(v_res_2416_);
return v_r_2417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2418_, lean_object* v_build_2419_, lean_object* v_cfg_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2422_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___closed__0));
v___x_2423_ = lean_st_mk_ref(v___x_2422_);
lean_inc(v___x_2423_);
v___x_2424_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2420_, v___x_2423_);
lean_inc_ref(v_cfg_2420_);
v___x_2425_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext(v_ws_2418_, v_cfg_2420_, v___x_2423_);
v___x_2426_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2427_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2425_, v_build_2419_, v___x_2426_);
v___x_2428_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2424_, v___x_2427_);
v___x_2429_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2420_, v___x_2425_, v___x_2424_, v___x_2428_);
lean_dec_ref(v___x_2425_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2430_, lean_object* v_build_2431_, lean_object* v_cfg_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lake_Workspace_runBuild___redArg(v_ws_2430_, v_build_2431_, v_cfg_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2435_, lean_object* v_ws_2436_, lean_object* v_build_2437_, lean_object* v_cfg_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lake_Workspace_runBuild___redArg(v_ws_2436_, v_build_2437_, v_cfg_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2441_, lean_object* v_ws_2442_, lean_object* v_build_2443_, lean_object* v_cfg_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lake_Workspace_runBuild(v_00_u03b1_2441_, v_ws_2442_, v_build_2443_, v_cfg_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2447_, lean_object* v_cfg_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; 
lean_inc(v_a_2449_);
v___x_2451_ = l_Lake_Workspace_runBuild___redArg(v_a_2449_, v_build_2447_, v_cfg_2448_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2452_, lean_object* v_cfg_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lake_runBuild___redArg(v_build_2452_, v_cfg_2453_, v_a_2454_);
lean_dec(v_a_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2457_, lean_object* v_build_2458_, lean_object* v_cfg_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v___x_2462_; 
lean_inc(v_a_2460_);
v___x_2462_ = l_Lake_Workspace_runBuild___redArg(v_a_2460_, v_build_2458_, v_cfg_2459_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_build_2464_, lean_object* v_cfg_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lake_runBuild(v_00_u03b1_2463_, v_build_2464_, v_cfg_2465_, v_a_2466_);
lean_dec(v_a_2466_);
return v_res_2468_;
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
