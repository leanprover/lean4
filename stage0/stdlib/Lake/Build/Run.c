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
static const lean_array_object l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "MACOSX_DEPLOYMENT_TARGET"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "99.0"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__4_value;
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
lean_object* v___x_263_; lean_object* v___x_7445__overap_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_7445__overap_264_ = lean_panic_fn_borrowed(v___x_263_, v_msg_261_);
v___x_265_ = lean_apply_1(v___x_7445__overap_264_, lean_box(0));
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
uint8_t v___y_13747__boxed_458_; uint8_t v_useAnsi_13748__boxed_459_; size_t v_i_boxed_460_; size_t v_stop_boxed_461_; lean_object* v_res_462_; 
v___y_13747__boxed_458_ = lean_unbox(v___y_450_);
v_useAnsi_13748__boxed_459_ = lean_unbox(v_useAnsi_451_);
v_i_boxed_460_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_449_, v___y_13747__boxed_458_, v_useAnsi_13748__boxed_459_, v_as_452_, v_i_boxed_460_, v_stop_boxed_461_, v_b_455_, v___y_456_);
lean_dec_ref(v_as_452_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* v_job_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___y_475_; lean_object* v___y_479_; lean_object* v_val_480_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v_jobNo_490_; lean_object* v_totalJobs_491_; uint8_t v_wantsRebuild_492_; lean_object* v_failures_493_; lean_object* v_resetCtrl_494_; lean_object* v_lastUpdate_495_; lean_object* v_spinnerIdx_496_; lean_object* v_out_497_; uint8_t v_outLv_498_; uint8_t v_failLv_499_; uint8_t v_minAction_500_; uint8_t v_showOptional_501_; uint8_t v_useAnsi_502_; uint8_t v_showProgress_503_; uint8_t v_showTime_504_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; uint8_t v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; uint8_t v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; uint8_t v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v_task_603_; lean_object* v_caption_604_; uint8_t v_optional_605_; uint8_t v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; uint8_t v___y_612_; lean_object* v___y_613_; uint8_t v___y_614_; uint32_t v___y_615_; uint8_t v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; uint8_t v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; uint32_t v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; uint8_t v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; uint32_t v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint8_t v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint32_t v___y_687_; uint8_t v___y_691_; lean_object* v___y_692_; uint8_t v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___y_696_; lean_object* v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; uint8_t v___y_701_; uint8_t v___y_707_; lean_object* v___y_708_; uint8_t v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; uint8_t v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; uint8_t v___y_716_; uint8_t v___y_717_; uint8_t v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_747_; lean_object* v___y_748_; uint8_t v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; uint8_t v___y_752_; uint8_t v___y_753_; uint8_t v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; uint8_t v___y_757_; uint8_t v___y_772_; uint8_t v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; uint8_t v___y_777_; uint8_t v___y_778_; uint8_t v___y_779_; lean_object* v___y_780_; uint8_t v___y_781_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; uint8_t v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; uint8_t v___y_794_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; uint8_t v___y_807_; lean_object* v___y_812_; lean_object* v___x_823_; lean_object* v_a_824_; 
v_jobNo_490_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_jobNo_490_);
v_totalJobs_491_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_totalJobs_491_);
v_wantsRebuild_492_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*6);
v_failures_493_ = lean_ctor_get(v_a_472_, 2);
v_resetCtrl_494_ = lean_ctor_get(v_a_472_, 3);
v_lastUpdate_495_ = lean_ctor_get(v_a_472_, 4);
v_spinnerIdx_496_ = lean_ctor_get(v_a_472_, 5);
v_out_497_ = lean_ctor_get(v_a_471_, 1);
v_outLv_498_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3);
v_failLv_499_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 1);
v_minAction_500_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 2);
v_showOptional_501_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 3);
v_useAnsi_502_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 4);
v_showProgress_503_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 5);
v_showTime_504_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*3 + 6);
v_task_603_ = lean_ctor_get(v_job_470_, 0);
lean_inc_ref(v_task_603_);
v_caption_604_ = lean_ctor_get(v_job_470_, 2);
lean_inc_ref(v_caption_604_);
v_optional_605_ = lean_ctor_get_uint8(v_job_470_, sizeof(void*)*3);
lean_dec_ref(v_job_470_);
v___x_823_ = lean_task_get_own(v_task_603_);
v_a_824_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___y_812_ = v_a_824_;
goto v___jp_811_;
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
lean_dec_ref_known(v___x_487_, 1);
v___y_479_ = v___y_484_;
v_val_480_ = v_a_488_;
goto v___jp_478_;
}
else
{
lean_object* v___x_489_; 
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = lean_box(0);
v___y_479_ = v___y_484_;
v_val_480_ = v___x_489_;
goto v___jp_478_;
}
}
v___jp_505_:
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_lt(v___y_510_, v___y_507_);
lean_dec(v___y_510_);
if (v___x_512_ == 0)
{
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
v___y_483_ = v___y_508_;
v___y_484_ = v___y_509_;
goto v___jp_482_;
}
else
{
lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v_snd_517_; 
v___x_513_ = lean_box(0);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___y_507_);
lean_dec(v___y_507_);
lean_inc_ref(v_out_497_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_497_, v___y_511_, v_useAnsi_502_, v___y_506_, v___x_514_, v___x_515_, v___x_513_, v___y_509_);
lean_dec_ref(v___y_506_);
v_snd_517_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_snd_517_);
lean_dec_ref(v___x_516_);
v___y_483_ = v___y_508_;
v___y_484_ = v_snd_517_;
goto v___jp_482_;
}
}
v___jp_518_:
{
if (v___y_523_ == 0)
{
lean_dec(v___y_525_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
v___y_483_ = v___y_522_;
v___y_484_ = v___y_524_;
goto v___jp_482_;
}
else
{
if (v___y_519_ == 0)
{
v___y_506_ = v___y_520_;
v___y_507_ = v___y_521_;
v___y_508_ = v___y_522_;
v___y_509_ = v___y_524_;
v___y_510_ = v___y_525_;
v___y_511_ = v_outLv_498_;
goto v___jp_505_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = 0;
v___y_506_ = v___y_520_;
v___y_507_ = v___y_521_;
v___y_508_ = v___y_522_;
v___y_509_ = v___y_524_;
v___y_510_ = v___y_525_;
v___y_511_ = v___x_526_;
goto v___jp_505_;
}
}
}
v___jp_527_:
{
lean_object* v_out_537_; lean_object* v_jobNo_538_; lean_object* v_totalJobs_539_; uint8_t v_wantsRebuild_540_; lean_object* v_failures_541_; lean_object* v_resetCtrl_542_; lean_object* v_lastUpdate_543_; lean_object* v_spinnerIdx_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_590_; 
v_out_537_ = lean_ctor_get(v___y_532_, 1);
v_jobNo_538_ = lean_ctor_get(v___y_534_, 0);
v_totalJobs_539_ = lean_ctor_get(v___y_534_, 1);
v_wantsRebuild_540_ = lean_ctor_get_uint8(v___y_534_, sizeof(void*)*6);
v_failures_541_ = lean_ctor_get(v___y_534_, 2);
v_resetCtrl_542_ = lean_ctor_get(v___y_534_, 3);
v_lastUpdate_543_ = lean_ctor_get(v___y_534_, 4);
v_spinnerIdx_544_ = lean_ctor_get(v___y_534_, 5);
v_isSharedCheck_590_ = !lean_is_exclusive(v___y_534_);
if (v_isSharedCheck_590_ == 0)
{
v___x_546_ = v___y_534_;
v_isShared_547_ = v_isSharedCheck_590_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_spinnerIdx_544_);
lean_inc(v_lastUpdate_543_);
lean_inc(v_resetCtrl_542_);
lean_inc(v_failures_541_);
lean_inc(v_totalJobs_539_);
lean_inc(v_jobNo_538_);
lean_dec(v___y_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_590_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_putStr_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v_putStr_548_ = lean_ctor_get(v_out_537_, 4);
v___x_549_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 3, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_jobNo_538_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_totalJobs_539_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_failures_541_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_lastUpdate_543_);
lean_ctor_set(v_reuseFailAlloc_589_, 5, v_spinnerIdx_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*6, v_wantsRebuild_540_);
v___x_551_ = v_reuseFailAlloc_589_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_string_append(v_resetCtrl_542_, v___y_536_);
lean_dec_ref(v___y_536_);
v___x_553_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_inc_ref(v_putStr_548_);
lean_inc_ref(v___x_554_);
v___x_555_ = lean_apply_2(v_putStr_548_, v___x_554_, lean_box(0));
if (lean_obj_tag(v___x_555_) == 0)
{
lean_dec_ref_known(v___x_555_, 1);
lean_dec_ref(v___x_554_);
v___y_519_ = v___y_529_;
v___y_520_ = v___y_528_;
v___y_521_ = v___y_530_;
v___y_522_ = v___y_532_;
v___y_523_ = v___y_533_;
v___y_524_ = v___x_551_;
v___y_525_ = v___y_535_;
goto v___jp_518_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_588_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_588_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_588_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_588_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_560_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_561_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_562_ = lean_unsigned_to_nat(89u);
v___x_563_ = lean_unsigned_to_nat(4u);
v___x_564_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_565_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6));
v___x_566_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11));
lean_inc(v___y_535_);
v___x_567_ = l_Lean_Name_num___override(v___x_566_, v___y_535_);
v___x_568_ = l_Lean_Name_str___override(v___x_567_, v___x_565_);
v___x_569_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14));
v___x_570_ = l_Lean_Name_str___override(v___x_568_, v___x_569_);
v___x_571_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_570_, v___y_531_);
v___x_572_ = lean_string_append(v___x_564_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
v___x_575_ = lean_io_error_to_string(v_a_556_);
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
lean_dec_ref(v___x_575_);
v___x_577_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_578_ = lean_string_append(v___x_576_, v___x_577_);
v___x_579_ = l_String_quote(v___x_554_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 3);
lean_ctor_set(v___x_558_, 0, v___x_579_);
v___x_581_ = v___x_558_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_587_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_582_ = l_Std_Format_defWidth;
lean_inc_n(v___y_535_, 2);
v___x_583_ = l_Std_Format_pretty(v___x_581_, v___x_582_, v___y_535_, v___y_535_);
v___x_584_ = lean_string_append(v___x_578_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = l_mkPanicMessageWithDecl(v___x_560_, v___x_561_, v___x_562_, v___x_563_, v___x_584_);
lean_dec_ref(v___x_584_);
v___x_586_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_585_);
v___y_519_ = v___y_529_;
v___y_520_ = v___y_528_;
v___y_521_ = v___y_530_;
v___y_522_ = v___y_532_;
v___y_523_ = v___y_533_;
v___y_524_ = v___x_551_;
v___y_525_ = v___y_535_;
goto v___jp_518_;
}
}
}
}
}
}
v___jp_591_:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lake_Ansi_chalk(v___y_601_, v___y_597_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_601_);
v___y_528_ = v___y_593_;
v___y_529_ = v___y_592_;
v___y_530_ = v___y_594_;
v___y_531_ = v___y_596_;
v___y_532_ = v___y_595_;
v___y_533_ = v___y_598_;
v___y_534_ = v___y_599_;
v___y_535_ = v___y_600_;
v___y_536_ = v___x_602_;
goto v___jp_527_;
}
v___jp_606_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_620_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_621_ = lean_string_push(v___x_620_, v___y_615_);
v___x_622_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
v___x_623_ = lean_string_append(v___x_621_, v___x_622_);
v___x_624_ = l_Nat_reprFast(v_jobNo_490_);
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
v___x_628_ = l_Nat_reprFast(v_totalJobs_491_);
v___x_629_ = lean_string_append(v___x_627_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_630_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
v___x_631_ = lean_string_append(v___x_629_, v___x_630_);
v___x_632_ = lean_string_append(v___x_631_, v___y_608_);
v___x_633_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = lean_string_append(v___x_634_, v___y_617_);
lean_dec_ref(v___y_617_);
v___x_636_ = lean_string_append(v___x_635_, v___x_633_);
v___x_637_ = lean_string_append(v___x_636_, v_caption_604_);
lean_dec_ref(v_caption_604_);
v___x_638_ = lean_string_append(v___x_637_, v___y_619_);
lean_dec_ref(v___y_619_);
if (v_useAnsi_502_ == 0)
{
v___y_528_ = v___y_609_;
v___y_529_ = v___y_614_;
v___y_530_ = v___y_610_;
v___y_531_ = v___y_616_;
v___y_532_ = v___y_611_;
v___y_533_ = v___y_612_;
v___y_534_ = v___y_613_;
v___y_535_ = v___y_618_;
v___y_536_ = v___x_638_;
goto v___jp_527_;
}
else
{
if (v___y_612_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
v___y_592_ = v___y_614_;
v___y_593_ = v___y_609_;
v___y_594_ = v___y_610_;
v___y_595_ = v___y_611_;
v___y_596_ = v___y_616_;
v___y_597_ = v___x_638_;
v___y_598_ = v___y_612_;
v___y_599_ = v___y_613_;
v___y_600_ = v___y_618_;
v___y_601_ = v___x_639_;
goto v___jp_591_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = l_Lake_LogLevel_ansiColor(v___y_607_);
v___y_592_ = v___y_614_;
v___y_593_ = v___y_609_;
v___y_594_ = v___y_610_;
v___y_595_ = v___y_611_;
v___y_596_ = v___y_616_;
v___y_597_ = v___x_638_;
v___y_598_ = v___y_612_;
v___y_599_ = v___y_613_;
v___y_600_ = v___y_618_;
v___y_601_ = v___x_640_;
goto v___jp_591_;
}
}
}
v___jp_641_:
{
lean_object* v___x_654_; 
v___x_654_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_607_ = v___y_642_;
v___y_608_ = v___y_643_;
v___y_609_ = v___y_644_;
v___y_610_ = v___y_645_;
v___y_611_ = v___y_646_;
v___y_612_ = v___y_647_;
v___y_613_ = v___y_648_;
v___y_614_ = v___y_649_;
v___y_615_ = v___y_650_;
v___y_616_ = v___y_651_;
v___y_617_ = v___y_652_;
v___y_618_ = v___y_653_;
v___y_619_ = v___x_654_;
goto v___jp_606_;
}
v___jp_655_:
{
if (v_showTime_504_ == 0)
{
lean_dec(v___y_661_);
v___y_642_ = v___y_656_;
v___y_643_ = v___y_668_;
v___y_644_ = v___y_657_;
v___y_645_ = v___y_658_;
v___y_646_ = v___y_659_;
v___y_647_ = v___y_660_;
v___y_648_ = v___y_662_;
v___y_649_ = v___y_663_;
v___y_650_ = v___y_664_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_667_;
goto v___jp_641_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_lt(v___y_667_, v___y_661_);
if (v___x_669_ == 0)
{
lean_dec(v___y_661_);
v___y_642_ = v___y_656_;
v___y_643_ = v___y_668_;
v___y_644_ = v___y_657_;
v___y_645_ = v___y_658_;
v___y_646_ = v___y_659_;
v___y_647_ = v___y_660_;
v___y_648_ = v___y_662_;
v___y_649_ = v___y_663_;
v___y_650_ = v___y_664_;
v___y_651_ = v___y_665_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_667_;
goto v___jp_641_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_670_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
v___x_671_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(v___y_661_);
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
v___y_607_ = v___y_656_;
v___y_608_ = v___y_668_;
v___y_609_ = v___y_657_;
v___y_610_ = v___y_658_;
v___y_611_ = v___y_659_;
v___y_612_ = v___y_660_;
v___y_613_ = v___y_662_;
v___y_614_ = v___y_663_;
v___y_615_ = v___y_664_;
v___y_616_ = v___y_665_;
v___y_617_ = v___y_666_;
v___y_618_ = v___y_667_;
v___y_619_ = v___x_674_;
goto v___jp_606_;
}
}
}
v___jp_675_:
{
if (v_optional_605_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___y_656_ = v___y_676_;
v___y_657_ = v___y_678_;
v___y_658_ = v___y_679_;
v___y_659_ = v___y_681_;
v___y_660_ = v___y_682_;
v___y_661_ = v___y_683_;
v___y_662_ = v___y_685_;
v___y_663_ = v___y_677_;
v___y_664_ = v___y_687_;
v___y_665_ = v___y_680_;
v___y_666_ = v___y_684_;
v___y_667_ = v___y_686_;
v___y_668_ = v___x_688_;
goto v___jp_655_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
v___y_656_ = v___y_676_;
v___y_657_ = v___y_678_;
v___y_658_ = v___y_679_;
v___y_659_ = v___y_681_;
v___y_660_ = v___y_682_;
v___y_661_ = v___y_683_;
v___y_662_ = v___y_685_;
v___y_663_ = v___y_677_;
v___y_664_ = v___y_687_;
v___y_665_ = v___y_680_;
v___y_666_ = v___y_684_;
v___y_667_ = v___y_686_;
v___y_668_ = v___x_689_;
goto v___jp_655_;
}
}
v___jp_690_:
{
if (v___y_696_ == 0)
{
if (v_showProgress_503_ == 0)
{
lean_dec(v___y_700_);
lean_dec(v___y_697_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_caption_604_);
lean_dec(v_totalJobs_491_);
lean_dec(v_jobNo_490_);
v___y_475_ = v___y_699_;
goto v___jp_474_;
}
else
{
if (v_useAnsi_502_ == 0)
{
if (v___y_698_ == 0)
{
lean_dec(v___y_700_);
lean_dec(v___y_697_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_caption_604_);
lean_dec(v_totalJobs_491_);
lean_dec(v_jobNo_490_);
v___y_475_ = v___y_699_;
goto v___jp_474_;
}
else
{
lean_object* v___x_702_; uint32_t v___x_703_; 
v___x_702_ = l_Lake_JobAction_verb(v___y_693_, v___y_701_);
v___x_703_ = 10004;
v___y_676_ = v___y_691_;
v___y_677_ = v___y_693_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_694_;
v___y_680_ = v___y_698_;
v___y_681_ = v___y_695_;
v___y_682_ = v___y_696_;
v___y_683_ = v___y_697_;
v___y_684_ = v___x_702_;
v___y_685_ = v___y_699_;
v___y_686_ = v___y_700_;
v___y_687_ = v___x_703_;
goto v___jp_675_;
}
}
else
{
lean_dec(v___y_700_);
lean_dec(v___y_697_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_caption_604_);
lean_dec(v_totalJobs_491_);
lean_dec(v_jobNo_490_);
v___y_475_ = v___y_699_;
goto v___jp_474_;
}
}
}
else
{
lean_object* v___x_704_; uint32_t v___x_705_; 
v___x_704_ = l_Lake_JobAction_verb(v___y_693_, v___y_701_);
v___x_705_ = l_Lake_LogLevel_icon(v___y_691_);
v___y_676_ = v___y_691_;
v___y_677_ = v___y_693_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_694_;
v___y_680_ = v___y_696_;
v___y_681_ = v___y_695_;
v___y_682_ = v___y_696_;
v___y_683_ = v___y_697_;
v___y_684_ = v___x_704_;
v___y_685_ = v___y_699_;
v___y_686_ = v___y_700_;
v___y_687_ = v___x_705_;
goto v___jp_675_;
}
}
v___jp_706_:
{
if (v_optional_605_ == 0)
{
v___y_691_ = v___y_707_;
v___y_692_ = v___y_708_;
v___y_693_ = v___y_709_;
v___y_694_ = v___y_710_;
v___y_695_ = v___y_711_;
v___y_696_ = v___y_717_;
v___y_697_ = v___y_713_;
v___y_698_ = v___y_712_;
v___y_699_ = v___y_714_;
v___y_700_ = v___y_715_;
v___y_701_ = v___y_716_;
goto v___jp_690_;
}
else
{
if (v_showOptional_501_ == 0)
{
lean_dec(v___y_715_);
lean_dec(v___y_713_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v_caption_604_);
lean_dec(v_totalJobs_491_);
lean_dec(v_jobNo_490_);
v___y_475_ = v___y_714_;
goto v___jp_474_;
}
else
{
v___y_691_ = v___y_707_;
v___y_692_ = v___y_708_;
v___y_693_ = v___y_709_;
v___y_694_ = v___y_710_;
v___y_695_ = v___y_711_;
v___y_696_ = v___y_717_;
v___y_697_ = v___y_713_;
v___y_698_ = v___y_712_;
v___y_699_ = v___y_714_;
v___y_700_ = v___y_715_;
v___y_701_ = v___y_716_;
goto v___jp_690_;
}
}
}
v___jp_718_:
{
if (v___y_720_ == 0)
{
if (v___y_726_ == 0)
{
v___y_707_ = v___y_719_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_720_;
v___y_710_ = v___y_722_;
v___y_711_ = v___y_729_;
v___y_712_ = v___y_723_;
v___y_713_ = v___y_724_;
v___y_714_ = v___y_730_;
v___y_715_ = v___y_727_;
v___y_716_ = v___y_728_;
v___y_717_ = v___y_726_;
goto v___jp_706_;
}
else
{
v___y_707_ = v___y_719_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_720_;
v___y_710_ = v___y_722_;
v___y_711_ = v___y_729_;
v___y_712_ = v___y_723_;
v___y_713_ = v___y_724_;
v___y_714_ = v___y_730_;
v___y_715_ = v___y_727_;
v___y_716_ = v___y_728_;
v___y_717_ = v___y_725_;
goto v___jp_706_;
}
}
else
{
if (v_optional_605_ == 0)
{
lean_object* v_jobNo_731_; lean_object* v_totalJobs_732_; uint8_t v_wantsRebuild_733_; lean_object* v_failures_734_; lean_object* v_resetCtrl_735_; lean_object* v_lastUpdate_736_; lean_object* v_spinnerIdx_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_jobNo_731_ = lean_ctor_get(v___y_730_, 0);
v_totalJobs_732_ = lean_ctor_get(v___y_730_, 1);
v_wantsRebuild_733_ = lean_ctor_get_uint8(v___y_730_, sizeof(void*)*6);
v_failures_734_ = lean_ctor_get(v___y_730_, 2);
v_resetCtrl_735_ = lean_ctor_get(v___y_730_, 3);
v_lastUpdate_736_ = lean_ctor_get(v___y_730_, 4);
v_spinnerIdx_737_ = lean_ctor_get(v___y_730_, 5);
v_isSharedCheck_745_ = !lean_is_exclusive(v___y_730_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v___y_730_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_spinnerIdx_737_);
lean_inc(v_lastUpdate_736_);
lean_inc(v_resetCtrl_735_);
lean_inc(v_failures_734_);
lean_inc(v_totalJobs_732_);
lean_inc(v_jobNo_731_);
lean_dec(v___y_730_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc_ref(v_caption_604_);
v___x_741_ = lean_array_push(v_failures_734_, v_caption_604_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 2, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_jobNo_731_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_totalJobs_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_resetCtrl_735_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_lastUpdate_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 5, v_spinnerIdx_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*6, v_wantsRebuild_733_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
v___y_707_ = v___y_719_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_720_;
v___y_710_ = v___y_722_;
v___y_711_ = v___y_729_;
v___y_712_ = v___y_723_;
v___y_713_ = v___y_724_;
v___y_714_ = v___x_743_;
v___y_715_ = v___y_727_;
v___y_716_ = v___y_728_;
v___y_717_ = v___y_720_;
goto v___jp_706_;
}
}
}
else
{
v___y_707_ = v___y_719_;
v___y_708_ = v___y_721_;
v___y_709_ = v___y_720_;
v___y_710_ = v___y_722_;
v___y_711_ = v___y_729_;
v___y_712_ = v___y_723_;
v___y_713_ = v___y_724_;
v___y_714_ = v___y_730_;
v___y_715_ = v___y_727_;
v___y_716_ = v___y_728_;
v___y_717_ = v___y_720_;
goto v___jp_706_;
}
}
}
v___jp_746_:
{
if (v___y_753_ == 0)
{
v___y_719_ = v___y_747_;
v___y_720_ = v___y_749_;
v___y_721_ = v___y_748_;
v___y_722_ = v___y_750_;
v___y_723_ = v___y_757_;
v___y_724_ = v___y_751_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_754_;
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v_a_471_;
v___y_730_ = v_a_472_;
goto v___jp_718_;
}
else
{
if (v_wantsRebuild_492_ == 0)
{
lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_inc(v_spinnerIdx_496_);
lean_inc(v_lastUpdate_495_);
lean_inc_ref(v_resetCtrl_494_);
lean_inc_ref(v_failures_493_);
v_isSharedCheck_764_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_765_ = lean_ctor_get(v_a_472_, 5);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_a_472_, 4);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_a_472_, 3);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_a_472_, 2);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_a_472_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_a_472_, 0);
lean_dec(v_unused_770_);
v___x_759_ = v_a_472_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_a_472_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
lean_inc(v_totalJobs_491_);
lean_inc(v_jobNo_490_);
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_jobNo_490_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_totalJobs_491_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_failures_493_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_resetCtrl_494_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_lastUpdate_495_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_spinnerIdx_496_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*6, v___y_753_);
v___y_719_ = v___y_747_;
v___y_720_ = v___y_749_;
v___y_721_ = v___y_748_;
v___y_722_ = v___y_750_;
v___y_723_ = v___y_757_;
v___y_724_ = v___y_751_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_754_;
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v_a_471_;
v___y_730_ = v___x_762_;
goto v___jp_718_;
}
}
}
else
{
v___y_719_ = v___y_747_;
v___y_720_ = v___y_749_;
v___y_721_ = v___y_748_;
v___y_722_ = v___y_750_;
v___y_723_ = v___y_757_;
v___y_724_ = v___y_751_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_754_;
v___y_727_ = v___y_755_;
v___y_728_ = v___y_756_;
v___y_729_ = v_a_471_;
v___y_730_ = v_a_472_;
goto v___jp_718_;
}
}
}
v___jp_771_:
{
uint8_t v___x_782_; 
v___x_782_ = l_Lake_instOrdJobAction_ord(v_minAction_500_, v___y_779_);
if (v___x_782_ == 2)
{
uint8_t v___x_783_; 
v___x_783_ = 0;
v___y_747_ = v___y_772_;
v___y_748_ = v___y_774_;
v___y_749_ = v___y_773_;
v___y_750_ = v___y_775_;
v___y_751_ = v___y_776_;
v___y_752_ = v___y_781_;
v___y_753_ = v___y_777_;
v___y_754_ = v___y_778_;
v___y_755_ = v___y_780_;
v___y_756_ = v___y_779_;
v___y_757_ = v___x_783_;
goto v___jp_746_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = 1;
v___y_747_ = v___y_772_;
v___y_748_ = v___y_774_;
v___y_749_ = v___y_773_;
v___y_750_ = v___y_775_;
v___y_751_ = v___y_776_;
v___y_752_ = v___y_781_;
v___y_753_ = v___y_777_;
v___y_754_ = v___y_778_;
v___y_755_ = v___y_780_;
v___y_756_ = v___y_779_;
v___y_757_ = v___x_784_;
goto v___jp_746_;
}
}
v___jp_785_:
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_strict_and(v___y_791_, v___y_794_);
v___x_796_ = l_Lake_instOrdLogLevel_ord(v_outLv_498_, v___y_786_);
if (v___x_796_ == 2)
{
uint8_t v___x_797_; 
v___x_797_ = 0;
v___y_772_ = v___y_786_;
v___y_773_ = v___x_795_;
v___y_774_ = v___y_787_;
v___y_775_ = v___y_788_;
v___y_776_ = v___y_789_;
v___y_777_ = v___y_790_;
v___y_778_ = v___y_791_;
v___y_779_ = v___y_793_;
v___y_780_ = v___y_792_;
v___y_781_ = v___x_797_;
goto v___jp_771_;
}
else
{
uint8_t v___x_798_; 
v___x_798_ = 1;
v___y_772_ = v___y_786_;
v___y_773_ = v___x_795_;
v___y_774_ = v___y_787_;
v___y_775_ = v___y_788_;
v___y_776_ = v___y_789_;
v___y_777_ = v___y_790_;
v___y_778_ = v___y_791_;
v___y_779_ = v___y_793_;
v___y_780_ = v___y_792_;
v___y_781_ = v___x_798_;
goto v___jp_771_;
}
}
v___jp_799_:
{
uint8_t v___x_808_; 
v___x_808_ = l_Lake_instOrdLogLevel_ord(v_failLv_499_, v___y_800_);
if (v___x_808_ == 2)
{
uint8_t v___x_809_; 
v___x_809_ = 0;
v___y_786_ = v___y_800_;
v___y_787_ = v___y_801_;
v___y_788_ = v___y_802_;
v___y_789_ = v___y_803_;
v___y_790_ = v___y_804_;
v___y_791_ = v___y_807_;
v___y_792_ = v___y_806_;
v___y_793_ = v___y_805_;
v___y_794_ = v___x_809_;
goto v___jp_785_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = 1;
v___y_786_ = v___y_800_;
v___y_787_ = v___y_801_;
v___y_788_ = v___y_802_;
v___y_789_ = v___y_803_;
v___y_790_ = v___y_804_;
v___y_791_ = v___y_807_;
v___y_792_ = v___y_806_;
v___y_793_ = v___y_805_;
v___y_794_ = v___x_810_;
goto v___jp_785_;
}
}
v___jp_811_:
{
lean_object* v_log_813_; uint8_t v_action_814_; uint8_t v_wantsRebuild_815_; lean_object* v_buildTime_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_log_813_ = lean_ctor_get(v___y_812_, 0);
lean_inc_ref(v_log_813_);
v_action_814_ = lean_ctor_get_uint8(v___y_812_, sizeof(void*)*3);
v_wantsRebuild_815_ = lean_ctor_get_uint8(v___y_812_, sizeof(void*)*3 + 1);
v_buildTime_816_ = lean_ctor_get(v___y_812_, 2);
lean_inc(v_buildTime_816_);
lean_dec_ref(v___y_812_);
v___x_817_ = l_Lake_Log_maxLv(v_log_813_);
v___x_818_ = lean_array_get_size(v_log_813_);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
uint8_t v___x_821_; 
v___x_821_ = 1;
v___y_800_ = v___x_817_;
v___y_801_ = v_log_813_;
v___y_802_ = v___x_818_;
v___y_803_ = v_buildTime_816_;
v___y_804_ = v_wantsRebuild_815_;
v___y_805_ = v_action_814_;
v___y_806_ = v___x_819_;
v___y_807_ = v___x_821_;
goto v___jp_799_;
}
else
{
uint8_t v___x_822_; 
v___x_822_ = 0;
v___y_800_ = v___x_817_;
v___y_801_ = v_log_813_;
v___y_802_ = v___x_818_;
v___y_803_ = v_buildTime_816_;
v___y_804_ = v_wantsRebuild_815_;
v___y_805_ = v_action_814_;
v___y_806_ = v___x_819_;
v___y_807_ = v___x_822_;
goto v___jp_799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* v_job_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_825_, v_a_826_, v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* v_out_830_, uint8_t v___y_831_, uint8_t v_useAnsi_832_, lean_object* v_as_833_, size_t v_i_834_, size_t v_stop_835_, lean_object* v_b_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_830_, v___y_831_, v_useAnsi_832_, v_as_833_, v_i_834_, v_stop_835_, v_b_836_, v___y_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* v_out_841_, lean_object* v___y_842_, lean_object* v_useAnsi_843_, lean_object* v_as_844_, lean_object* v_i_845_, lean_object* v_stop_846_, lean_object* v_b_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___y_14507__boxed_851_; uint8_t v_useAnsi_14508__boxed_852_; size_t v_i_boxed_853_; size_t v_stop_boxed_854_; lean_object* v_res_855_; 
v___y_14507__boxed_851_ = lean_unbox(v___y_842_);
v_useAnsi_14508__boxed_852_ = lean_unbox(v_useAnsi_843_);
v_i_boxed_853_ = lean_unbox_usize(v_i_845_);
lean_dec(v_i_845_);
v_stop_boxed_854_ = lean_unbox_usize(v_stop_846_);
lean_dec(v_stop_846_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_841_, v___y_14507__boxed_851_, v_useAnsi_14508__boxed_852_, v_as_844_, v_i_boxed_853_, v_stop_boxed_854_, v_b_847_, v___y_848_, v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v_as_844_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_jobs_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_jobNo_863_; lean_object* v_totalJobs_864_; uint8_t v_wantsRebuild_865_; lean_object* v_failures_866_; lean_object* v_resetCtrl_867_; lean_object* v_lastUpdate_868_; lean_object* v_spinnerIdx_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_879_; 
v_jobs_859_ = lean_ctor_get(v_a_856_, 0);
v___x_860_ = lean_st_ref_take(v_jobs_859_);
v___x_861_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
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
lean_object* v___x_1036_; lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
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
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_array_get_size(v_snd_1040_);
v___x_1043_ = lean_nat_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_fst_1039_);
v___x_1044_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1033_, v_snd_1038_);
v_fst_1045_ = lean_ctor_get(v___x_1044_, 0);
v_snd_1046_ = lean_ctor_get(v___x_1044_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1048_ = v___x_1044_;
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v___x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1057_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_fst_1045_);
v___x_1051_ = lean_nat_dec_lt(v___x_1041_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_dec(v_fst_1045_);
lean_dec(v_snd_1040_);
v___x_1052_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1052_);
v___x_1054_ = v___x_1048_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_snd_1046_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
lean_del_object(v___x_1048_);
v_new_1031_ = v_fst_1045_;
v_unfinished_1032_ = v_snd_1040_;
v_a_1034_ = v_snd_1046_;
goto _start;
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v_snd_1059_; lean_object* v___x_1060_; lean_object* v_snd_1061_; lean_object* v___x_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; 
v___x_1058_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(v_fst_1039_, v_snd_1040_, v_a_1033_, v_snd_1038_);
lean_dec(v_fst_1039_);
v_snd_1059_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_snd_1059_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_1033_, v_snd_1059_);
v_snd_1061_ = lean_ctor_get(v___x_1060_, 1);
lean_inc(v_snd_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_1033_, v_snd_1061_);
v_fst_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_snd_1064_);
lean_dec_ref(v___x_1062_);
v_new_1031_ = v_fst_1063_;
v_unfinished_1032_ = v_snd_1040_;
v_a_1034_ = v_snd_1064_;
goto _start;
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
v___x_1122_ = lean_unsigned_to_nat(89u);
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0(void){
_start:
{
uint8_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = 2;
v___x_1162_ = l_Lake_Verbosity_ctorIdx(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* v_cfg_1163_, lean_object* v_jobs_1164_){
_start:
{
lean_object* v_toLogConfig_1166_; uint8_t v_verbosity_1167_; uint8_t v_failLv_1168_; uint8_t v_outLv_1169_; uint8_t v_ansiMode_1170_; lean_object* v_out_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___y_1179_; uint8_t v___y_1180_; uint8_t v___y_1184_; 
v_toLogConfig_1166_ = lean_ctor_get(v_cfg_1163_, 0);
v_verbosity_1167_ = lean_ctor_get_uint8(v_cfg_1163_, sizeof(void*)*4 + 3);
v_failLv_1168_ = lean_ctor_get_uint8(v_toLogConfig_1166_, sizeof(void*)*1);
v_outLv_1169_ = lean_ctor_get_uint8(v_toLogConfig_1166_, sizeof(void*)*1 + 1);
v_ansiMode_1170_ = lean_ctor_get_uint8(v_toLogConfig_1166_, sizeof(void*)*1 + 2);
v_out_1171_ = lean_ctor_get(v_toLogConfig_1166_, 0);
v___x_1172_ = l_Lake_OutStream_get(v_out_1171_);
lean_inc_ref(v___x_1172_);
v___x_1173_ = l_Lake_AnsiMode_isEnabled(v___x_1172_, v_ansiMode_1170_);
v___x_1174_ = l_Lake_BuildConfig_showProgress(v_cfg_1163_);
v___x_1175_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1167_);
v___x_1176_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0, &l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_mkMonitorContext___closed__0);
v___x_1177_ = lean_nat_dec_eq(v___x_1175_, v___x_1176_);
lean_dec(v___x_1175_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1186_; 
v___x_1186_ = 3;
v___y_1184_ = v___x_1186_;
goto v___jp_1183_;
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = 0;
v___y_1184_ = v___x_1187_;
goto v___jp_1183_;
}
v___jp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_unsigned_to_nat(100u);
v___x_1182_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v___x_1182_, 0, v_jobs_1164_);
lean_ctor_set(v___x_1182_, 1, v___x_1172_);
lean_ctor_set(v___x_1182_, 2, v___x_1181_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3, v_outLv_1169_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 1, v_failLv_1168_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 2, v___y_1179_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 3, v___x_1177_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 4, v___x_1173_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 5, v___x_1174_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 6, v___y_1180_);
return v___x_1182_;
}
v___jp_1183_:
{
if (v___x_1177_ == 0)
{
if (v___x_1173_ == 0)
{
uint8_t v___x_1185_; 
v___x_1185_ = 1;
v___y_1179_ = v___y_1184_;
v___y_1180_ = v___x_1185_;
goto v___jp_1178_;
}
else
{
v___y_1179_ = v___y_1184_;
v___y_1180_ = v___x_1177_;
goto v___jp_1178_;
}
}
else
{
v___y_1179_ = v___y_1184_;
v___y_1180_ = v___x_1177_;
goto v___jp_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* v_cfg_1188_, lean_object* v_jobs_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_1188_, v_jobs_1189_);
lean_dec_ref(v_cfg_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* v_ctx_1192_, lean_object* v_initJobs_1193_, lean_object* v_initFailures_1194_, lean_object* v_resetCtrl_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_snd_1202_; lean_object* v_totalJobs_1203_; uint8_t v_wantsRebuild_1204_; lean_object* v_failures_1205_; lean_object* v___x_1206_; 
v___x_1197_ = lean_io_mono_ms_now();
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = 0;
v___x_1200_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
lean_ctor_set(v___x_1200_, 2, v_initFailures_1194_);
lean_ctor_set(v___x_1200_, 3, v_resetCtrl_1195_);
lean_ctor_set(v___x_1200_, 4, v___x_1197_);
lean_ctor_set(v___x_1200_, 5, v___x_1198_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*6, v___x_1199_);
v___x_1201_ = l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_1193_, v_ctx_1192_, v___x_1200_);
v_snd_1202_ = lean_ctor_get(v___x_1201_, 1);
lean_inc(v_snd_1202_);
lean_dec_ref(v___x_1201_);
v_totalJobs_1203_ = lean_ctor_get(v_snd_1202_, 1);
lean_inc(v_totalJobs_1203_);
v_wantsRebuild_1204_ = lean_ctor_get_uint8(v_snd_1202_, sizeof(void*)*6);
v_failures_1205_ = lean_ctor_get(v_snd_1202_, 2);
lean_inc_ref(v_failures_1205_);
lean_dec(v_snd_1202_);
v___x_1206_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1206_, 0, v_failures_1205_);
lean_ctor_set(v___x_1206_, 1, v_totalJobs_1203_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*2, v_wantsRebuild_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* v_ctx_1207_, lean_object* v_initJobs_1208_, lean_object* v_initFailures_1209_, lean_object* v_resetCtrl_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1207_, v_initJobs_1208_, v_initFailures_1209_, v_resetCtrl_1210_);
lean_dec_ref(v_ctx_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* v_initJobs_1213_, lean_object* v_jobs_1214_, lean_object* v_out_1215_, uint8_t v_failLv_1216_, uint8_t v_outLv_1217_, uint8_t v_minAction_1218_, uint8_t v_showOptional_1219_, uint8_t v_useAnsi_1220_, uint8_t v_showProgress_1221_, uint8_t v_showTime_1222_, lean_object* v_resetCtrl_1223_, lean_object* v_initFailures_1224_, lean_object* v_updateFrequency_1225_){
_start:
{
lean_object* v_ctx_1227_; lean_object* v___x_1228_; 
v_ctx_1227_ = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(v_ctx_1227_, 0, v_jobs_1214_);
lean_ctor_set(v_ctx_1227_, 1, v_out_1215_);
lean_ctor_set(v_ctx_1227_, 2, v_updateFrequency_1225_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3, v_outLv_1217_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3 + 1, v_failLv_1216_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3 + 2, v_minAction_1218_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3 + 3, v_showOptional_1219_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3 + 4, v_useAnsi_1220_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3 + 5, v_showProgress_1221_);
lean_ctor_set_uint8(v_ctx_1227_, sizeof(void*)*3 + 6, v_showTime_1222_);
v___x_1228_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1227_, v_initJobs_1213_, v_initFailures_1224_, v_resetCtrl_1223_);
lean_dec_ref_known(v_ctx_1227_, 3);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* v_initJobs_1229_, lean_object* v_jobs_1230_, lean_object* v_out_1231_, lean_object* v_failLv_1232_, lean_object* v_outLv_1233_, lean_object* v_minAction_1234_, lean_object* v_showOptional_1235_, lean_object* v_useAnsi_1236_, lean_object* v_showProgress_1237_, lean_object* v_showTime_1238_, lean_object* v_resetCtrl_1239_, lean_object* v_initFailures_1240_, lean_object* v_updateFrequency_1241_, lean_object* v_a_1242_){
_start:
{
uint8_t v_failLv_boxed_1243_; uint8_t v_outLv_boxed_1244_; uint8_t v_minAction_boxed_1245_; uint8_t v_showOptional_boxed_1246_; uint8_t v_useAnsi_boxed_1247_; uint8_t v_showProgress_boxed_1248_; uint8_t v_showTime_boxed_1249_; lean_object* v_res_1250_; 
v_failLv_boxed_1243_ = lean_unbox(v_failLv_1232_);
v_outLv_boxed_1244_ = lean_unbox(v_outLv_1233_);
v_minAction_boxed_1245_ = lean_unbox(v_minAction_1234_);
v_showOptional_boxed_1246_ = lean_unbox(v_showOptional_1235_);
v_useAnsi_boxed_1247_ = lean_unbox(v_useAnsi_1236_);
v_showProgress_boxed_1248_ = lean_unbox(v_showProgress_1237_);
v_showTime_boxed_1249_ = lean_unbox(v_showTime_1238_);
v_res_1250_ = l_Lake_monitorJobs(v_initJobs_1229_, v_jobs_1230_, v_out_1231_, v_failLv_boxed_1243_, v_outLv_boxed_1244_, v_minAction_boxed_1245_, v_showOptional_boxed_1246_, v_useAnsi_boxed_1247_, v_showProgress_boxed_1248_, v_showTime_boxed_1249_, v_resetCtrl_1239_, v_initFailures_1240_, v_updateFrequency_1241_);
return v_res_1250_;
}
}
static uint32_t _init_l_Lake_noBuildCode(void){
_start:
{
uint32_t v___x_1251_; 
v___x_1251_ = 3;
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* v_logger_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_apply_2(v_logger_1252_, v___y_1254_, lean_box(0));
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* v_logger_1257_, lean_object* v_x_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(v_logger_1257_, v_x_1258_, v___y_1259_);
return v_res_1261_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1272_ = l_String_quote(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5);
v___x_1274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = l_Std_Format_defWidth;
v___x_1277_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
v___x_1278_ = l_Std_Format_pretty(v___x_1277_, v___x_1276_, v___x_1275_, v___x_1275_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_1281_ = l_String_quote(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9);
v___x_1283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = l_Std_Format_defWidth;
v___x_1286_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
v___x_1287_ = l_Std_Format_pretty(v___x_1286_, v___x_1285_, v___x_1284_, v___x_1284_);
return v___x_1287_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_1290_ = l_String_quote(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13);
v___x_1292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = l_Std_Format_defWidth;
v___x_1295_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
v___x_1296_ = l_Std_Format_pretty(v___x_1295_, v___x_1294_, v___x_1293_, v___x_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* v_logger_1298_, lean_object* v_ws_1299_, lean_object* v_outputsRef_x3f_1300_, lean_object* v_out_1301_, lean_object* v_outputsFile_1302_, uint8_t v_isVerbose_1303_){
_start:
{
lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___x_1411_; 
lean_inc_ref(v_logger_1298_);
v___f_1307_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1307_, 0, v_logger_1298_);
v___x_1308_ = l_instMonadBaseIO;
v___x_1411_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1299_);
if (v___x_1411_ == 0)
{
lean_object* v_packages_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_baseName_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_packages_1412_ = lean_ctor_get(v_ws_1299_, 4);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_array_fget_borrowed(v_packages_1412_, v___x_1413_);
v_baseName_1415_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_baseName_1415_);
v___x_1416_ = l_Lean_Name_toString(v_baseName_1415_, v___x_1411_);
v___x_1417_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16));
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
v___x_1419_ = 2;
v___x_1420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*1, v___x_1419_);
v___x_1421_ = lean_apply_2(v_logger_1298_, v___x_1420_, lean_box(0));
goto v___jp_1330_;
}
else
{
lean_dec_ref(v_logger_1298_);
goto v___jp_1330_;
}
v___jp_1305_:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
v___jp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_array_get_size(v___y_1311_);
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_nat_dec_lt(v___y_1310_, v___x_1312_);
if (v___x_1314_ == 0)
{
lean_dec_ref(v___y_1311_);
lean_dec_ref(v___f_1307_);
return v___x_1313_;
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1374__overap_1317_; lean_object* v___x_1318_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1312_);
v___x_1374__overap_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1308_, v___f_1307_, v___y_1311_, v___x_1315_, v___x_1316_, v___x_1313_);
v___x_1318_ = lean_apply_1(v___x_1374__overap_1317_, lean_box(0));
return v___x_1318_;
}
}
v___jp_1319_:
{
if (v_isVerbose_1303_ == 0)
{
lean_object* v___x_1322_; 
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___f_1307_);
v___x_1322_ = lean_box(0);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_array_get_size(v___y_1321_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_nat_dec_lt(v___y_1320_, v___x_1323_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___f_1307_);
return v___x_1324_;
}
else
{
size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1305__overap_1328_; lean_object* v___x_1329_; 
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = lean_usize_of_nat(v___x_1323_);
v___x_1305__overap_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1308_, v___f_1307_, v___y_1321_, v___x_1326_, v___x_1327_, v___x_1324_);
v___x_1329_ = lean_apply_1(v___x_1305__overap_1328_, lean_box(0));
return v___x_1329_;
}
}
}
v___jp_1330_:
{
if (lean_obj_tag(v_outputsRef_x3f_1300_) == 1)
{
lean_object* v_val_1331_; lean_object* v___x_1332_; lean_object* v_packages_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_config_1336_; lean_object* v_toLeanConfig_1337_; lean_object* v_platformIndependent_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_val_1331_ = lean_ctor_get(v_outputsRef_x3f_1300_, 0);
v___x_1332_ = lean_st_ref_get(v_val_1331_);
v_packages_1333_ = lean_ctor_get(v_ws_1299_, 4);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_array_fget_borrowed(v_packages_1333_, v___x_1334_);
v_config_1336_ = lean_ctor_get(v___x_1335_, 6);
v_toLeanConfig_1337_ = lean_ctor_get(v_config_1336_, 1);
v_platformIndependent_1338_ = lean_ctor_get(v_toLeanConfig_1337_, 10);
v___f_1339_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
v___x_1340_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
lean_inc(v_platformIndependent_1338_);
v___x_1341_ = l_Option_instBEq_beq___redArg(v___f_1339_, v_platformIndependent_1338_, v___x_1340_);
v___x_1342_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1343_ = l_Lake_CacheMap_writeFile(v_outputsFile_1302_, v___x_1332_, v___x_1341_, v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 1);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 2);
v___x_1345_ = lean_array_get_size(v_a_1344_);
v___x_1346_ = lean_nat_dec_eq(v___x_1345_, v___x_1334_);
if (v___x_1346_ == 0)
{
if (v_isVerbose_1303_ == 0)
{
lean_dec(v_a_1344_);
lean_dec_ref(v___f_1307_);
lean_dec_ref(v_out_1301_);
goto v___jp_1305_;
}
else
{
lean_object* v_putStr_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_putStr_1347_ = lean_ctor_get(v_out_1301_, 4);
lean_inc_ref(v_putStr_1347_);
lean_dec_ref(v_out_1301_);
v___x_1348_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1349_ = lean_apply_2(v_putStr_1347_, v___x_1348_, lean_box(0));
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref_known(v___x_1349_, 1);
v___y_1310_ = v___x_1334_;
v___y_1311_ = v_a_1344_;
goto v___jp_1309_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1569__overap_1369_; lean_object* v___x_1370_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1352_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1354_ = lean_unsigned_to_nat(89u);
v___x_1355_ = lean_unsigned_to_nat(4u);
v___x_1356_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1357_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1357_, v_isVerbose_1303_);
v___x_1359_ = lean_string_append(v___x_1356_, v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_io_error_to_string(v_a_1350_);
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
v___x_1366_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
v___x_1368_ = l_mkPanicMessageWithDecl(v___x_1352_, v___x_1353_, v___x_1354_, v___x_1355_, v___x_1367_);
lean_dec_ref(v___x_1367_);
v___x_1569__overap_1369_ = l_panic___redArg(v___x_1351_, v___x_1368_);
v___x_1370_ = lean_apply_1(v___x_1569__overap_1369_, lean_box(0));
v___y_1310_ = v___x_1334_;
v___y_1311_ = v_a_1344_;
goto v___jp_1309_;
}
}
}
else
{
lean_dec(v_a_1344_);
lean_dec_ref(v___f_1307_);
lean_dec_ref(v_out_1301_);
goto v___jp_1305_;
}
}
else
{
lean_object* v_a_1371_; lean_object* v_putStr_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_a_1371_ = lean_ctor_get(v___x_1343_, 1);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1343_, 2);
v_putStr_1372_ = lean_ctor_get(v_out_1301_, 4);
lean_inc_ref(v_putStr_1372_);
lean_dec_ref(v_out_1301_);
v___x_1373_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_1374_ = lean_apply_2(v_putStr_1372_, v___x_1373_, lean_box(0));
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_dec_ref_known(v___x_1374_, 1);
v___y_1320_ = v___x_1334_;
v___y_1321_ = v_a_1371_;
goto v___jp_1319_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1354__overap_1389_; lean_object* v___x_1390_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1377_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1378_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1379_ = lean_unsigned_to_nat(89u);
v___x_1380_ = lean_unsigned_to_nat(4u);
v___x_1381_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1382_ = lean_io_error_to_string(v_a_1375_);
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
v___x_1386_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
v___x_1388_ = l_mkPanicMessageWithDecl(v___x_1377_, v___x_1378_, v___x_1379_, v___x_1380_, v___x_1387_);
lean_dec_ref(v___x_1387_);
v___x_1354__overap_1389_ = l_panic___redArg(v___x_1376_, v___x_1388_);
v___x_1390_ = lean_apply_1(v___x_1354__overap_1389_, lean_box(0));
v___y_1320_ = v___x_1334_;
v___y_1321_ = v_a_1371_;
goto v___jp_1319_;
}
}
}
else
{
lean_object* v_putStr_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v___f_1307_);
lean_dec_ref(v_outputsFile_1302_);
v_putStr_1391_ = lean_ctor_get(v_out_1301_, 4);
lean_inc_ref(v_putStr_1391_);
lean_dec_ref(v_out_1301_);
v___x_1392_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_1393_ = lean_apply_2(v_putStr_1391_, v___x_1392_, lean_box(0));
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
return v_a_1394_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1472__overap_1409_; lean_object* v___x_1410_; 
v_a_1395_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1396_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
v___x_1397_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1398_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1399_ = lean_unsigned_to_nat(89u);
v___x_1400_ = lean_unsigned_to_nat(4u);
v___x_1401_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1402_ = lean_io_error_to_string(v_a_1395_);
v___x_1403_ = lean_string_append(v___x_1401_, v___x_1402_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
v___x_1406_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15);
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
v___x_1408_ = l_mkPanicMessageWithDecl(v___x_1397_, v___x_1398_, v___x_1399_, v___x_1400_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1472__overap_1409_ = l_panic___redArg(v___x_1396_, v___x_1408_);
v___x_1410_ = lean_apply_1(v___x_1472__overap_1409_, lean_box(0));
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* v_logger_1422_, lean_object* v_ws_1423_, lean_object* v_outputsRef_x3f_1424_, lean_object* v_out_1425_, lean_object* v_outputsFile_1426_, lean_object* v_isVerbose_1427_, lean_object* v_a_1428_){
_start:
{
uint8_t v_isVerbose_boxed_1429_; lean_object* v_res_1430_; 
v_isVerbose_boxed_1429_ = lean_unbox(v_isVerbose_1427_);
v_res_1430_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(v_logger_1422_, v_ws_1423_, v_outputsRef_x3f_1424_, v_out_1425_, v_outputsFile_1426_, v_isVerbose_boxed_1429_);
lean_dec(v_outputsRef_x3f_1424_);
lean_dec_ref(v_ws_1423_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* v_out_1432_, lean_object* v_as_1433_, size_t v_i_1434_, size_t v_stop_1435_, lean_object* v_b_1436_){
_start:
{
lean_object* v_val_1439_; uint8_t v___x_1443_; 
v___x_1443_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
if (v___x_1443_ == 0)
{
lean_object* v_putStr_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_putStr_1444_ = lean_ctor_get(v_out_1432_, 4);
v___x_1445_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
v___x_1446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
v___x_1447_ = lean_string_append(v___x_1446_, v___x_1445_);
v___x_1448_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
v___x_1449_ = lean_string_append(v___x_1447_, v___x_1448_);
lean_inc_ref(v_putStr_1444_);
lean_inc_ref(v___x_1449_);
v___x_1450_ = lean_apply_2(v_putStr_1444_, v___x_1449_, lean_box(0));
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; 
lean_dec_ref(v___x_1449_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v_val_1439_ = v_a_1451_;
goto v___jp_1438_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1475_; 
v_a_1452_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1454_ = v___x_1450_;
v_isShared_1455_ = v_isSharedCheck_1475_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1450_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1475_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1456_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1457_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1458_ = lean_unsigned_to_nat(89u);
v___x_1459_ = lean_unsigned_to_nat(4u);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1462_ = lean_io_error_to_string(v_a_1452_);
v___x_1463_ = lean_string_append(v___x_1461_, v___x_1462_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1465_ = lean_string_append(v___x_1463_, v___x_1464_);
v___x_1466_ = l_String_quote(v___x_1449_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 3);
lean_ctor_set(v___x_1454_, 0, v___x_1466_);
v___x_1468_ = v___x_1454_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1469_ = l_Std_Format_defWidth;
v___x_1470_ = l_Std_Format_pretty(v___x_1468_, v___x_1469_, v___x_1460_, v___x_1460_);
v___x_1471_ = lean_string_append(v___x_1465_, v___x_1470_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1456_, v___x_1457_, v___x_1458_, v___x_1459_, v___x_1471_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1472_);
v_val_1439_ = v___x_1473_;
goto v___jp_1438_;
}
}
}
}
else
{
lean_dec_ref(v_out_1432_);
return v_b_1436_;
}
v___jp_1438_:
{
size_t v___x_1440_; size_t v___x_1441_; 
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_add(v_i_1434_, v___x_1440_);
v_i_1434_ = v___x_1441_;
v_b_1436_ = v_val_1439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* v_out_1476_, lean_object* v_as_1477_, lean_object* v_i_1478_, lean_object* v_stop_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_){
_start:
{
size_t v_i_boxed_1482_; size_t v_stop_boxed_1483_; lean_object* v_res_1484_; 
v_i_boxed_1482_ = lean_unbox_usize(v_i_1478_);
lean_dec(v_i_1478_);
v_stop_boxed_1483_ = lean_unbox_usize(v_stop_1479_);
lean_dec(v_stop_1479_);
v_res_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1476_, v_as_1477_, v_i_boxed_1482_, v_stop_boxed_1483_, v_b_1480_);
lean_dec_ref(v_as_1477_);
return v_res_1484_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1492_ = l_String_quote(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
v___x_1494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l_Std_Format_defWidth;
v___x_1497_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
v___x_1498_ = l_Std_Format_pretty(v___x_1497_, v___x_1496_, v___x_1495_, v___x_1495_);
return v___x_1498_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
v___x_1501_ = l_String_quote(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__10, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10);
v___x_1503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = l_Std_Format_defWidth;
v___x_1506_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__11, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11);
v___x_1507_ = l_Std_Format_pretty(v___x_1506_, v___x_1505_, v___x_1504_, v___x_1504_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* v_cfg_1508_, lean_object* v_out_1509_, lean_object* v_result_1510_){
_start:
{
uint8_t v___y_1513_; lean_object* v___y_1514_; lean_object* v_failures_1588_; lean_object* v_numJobs_1589_; uint8_t v___y_1591_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_failures_1588_ = lean_ctor_get(v_result_1510_, 0);
lean_inc_ref(v_failures_1588_);
v_numJobs_1589_ = lean_ctor_get(v_result_1510_, 1);
lean_inc(v_numJobs_1589_);
lean_dec_ref(v_result_1510_);
v___x_1624_ = lean_array_get_size(v_failures_1588_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_nat_dec_eq(v___x_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v_flush_1627_; lean_object* v_putStr_1628_; lean_object* v___y_1634_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_numJobs_1589_);
v_flush_1627_ = lean_ctor_get(v_out_1509_, 0);
lean_inc_ref(v_flush_1627_);
v_putStr_1628_ = lean_ctor_get(v_out_1509_, 4);
v___x_1645_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9));
lean_inc_ref(v_putStr_1628_);
v___x_1646_ = lean_apply_2(v_putStr_1628_, v___x_1645_, lean_box(0));
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref_known(v___x_1646_, 1);
goto v___jp_1635_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1649_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1650_ = lean_unsigned_to_nat(89u);
v___x_1651_ = lean_unsigned_to_nat(4u);
v___x_1652_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_1653_ = lean_io_error_to_string(v_a_1647_);
v___x_1654_ = lean_string_append(v___x_1652_, v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1656_ = lean_string_append(v___x_1654_, v___x_1655_);
v___x_1657_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__12, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12);
v___x_1658_ = lean_string_append(v___x_1656_, v___x_1657_);
v___x_1659_ = l_mkPanicMessageWithDecl(v___x_1648_, v___x_1649_, v___x_1650_, v___x_1651_, v___x_1658_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1659_);
goto v___jp_1635_;
}
v___jp_1629_:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_apply_1(v_flush_1627_, lean_box(0));
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
return v_a_1631_;
}
else
{
lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = lean_box(0);
return v___x_1632_;
}
}
v___jp_1633_:
{
goto v___jp_1629_;
}
v___jp_1635_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_nat_dec_lt(v___x_1625_, v___x_1624_);
if (v___x_1636_ == 0)
{
lean_dec_ref(v_failures_1588_);
lean_dec_ref(v_out_1509_);
goto v___jp_1629_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_nat_dec_le(v___x_1624_, v___x_1624_);
if (v___x_1638_ == 0)
{
if (v___x_1636_ == 0)
{
lean_dec_ref(v_failures_1588_);
lean_dec_ref(v_out_1509_);
goto v___jp_1629_;
}
else
{
size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = lean_usize_of_nat(v___x_1624_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1509_, v_failures_1588_, v___x_1639_, v___x_1640_, v___x_1637_);
lean_dec_ref(v_failures_1588_);
v___y_1634_ = v___x_1641_;
goto v___jp_1633_;
}
}
else
{
size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = lean_usize_of_nat(v___x_1624_);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_1509_, v_failures_1588_, v___x_1642_, v___x_1643_, v___x_1637_);
lean_dec_ref(v_failures_1588_);
v___y_1634_ = v___x_1644_;
goto v___jp_1633_;
}
}
}
}
else
{
uint8_t v___x_1661_; 
lean_dec_ref(v_failures_1588_);
v___x_1661_ = l_Lake_BuildConfig_showProgress(v_cfg_1508_);
if (v___x_1661_ == 0)
{
v___y_1591_ = v___x_1661_;
goto v___jp_1590_;
}
else
{
uint8_t v_showSuccess_1662_; 
v_showSuccess_1662_ = lean_ctor_get_uint8(v_cfg_1508_, sizeof(void*)*4 + 4);
v___y_1591_ = v_showSuccess_1662_;
goto v___jp_1590_;
}
}
v___jp_1512_:
{
uint8_t v_noBuild_1515_; 
v_noBuild_1515_ = lean_ctor_get_uint8(v_cfg_1508_, sizeof(void*)*4 + 2);
if (v_noBuild_1515_ == 0)
{
lean_object* v_putStr_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_putStr_1516_ = lean_ctor_get(v_out_1509_, 4);
lean_inc_ref(v_putStr_1516_);
lean_dec_ref(v_out_1509_);
v___x_1517_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
v___x_1518_ = lean_string_append(v___x_1517_, v___y_1514_);
lean_dec_ref(v___y_1514_);
v___x_1519_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
lean_inc_ref(v___x_1520_);
v___x_1521_ = lean_apply_2(v_putStr_1516_, v___x_1520_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; 
lean_dec_ref(v___x_1520_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
return v_a_1522_;
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1551_; 
v_a_1523_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1525_ = v___x_1521_;
v_isShared_1526_ = v_isSharedCheck_1551_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1551_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1527_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1528_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1529_ = lean_unsigned_to_nat(89u);
v___x_1530_ = lean_unsigned_to_nat(4u);
v___x_1531_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1533_, v___y_1513_);
v___x_1535_ = lean_string_append(v___x_1531_, v___x_1534_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1537_ = lean_string_append(v___x_1535_, v___x_1536_);
v___x_1538_ = lean_io_error_to_string(v_a_1523_);
v___x_1539_ = lean_string_append(v___x_1537_, v___x_1538_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
v___x_1542_ = l_String_quote(v___x_1520_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 3);
lean_ctor_set(v___x_1525_, 0, v___x_1542_);
v___x_1544_ = v___x_1525_;
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
v___x_1546_ = l_Std_Format_pretty(v___x_1544_, v___x_1545_, v___x_1532_, v___x_1532_);
v___x_1547_ = lean_string_append(v___x_1541_, v___x_1546_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = l_mkPanicMessageWithDecl(v___x_1527_, v___x_1528_, v___x_1529_, v___x_1530_, v___x_1547_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1548_);
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_putStr_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_putStr_1552_ = lean_ctor_get(v_out_1509_, 4);
lean_inc_ref(v_putStr_1552_);
lean_dec_ref(v_out_1509_);
v___x_1553_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
v___x_1554_ = lean_string_append(v___x_1553_, v___y_1514_);
lean_dec_ref(v___y_1514_);
v___x_1555_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
v___x_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
lean_inc_ref(v___x_1556_);
v___x_1557_ = lean_apply_2(v_putStr_1552_, v___x_1556_, lean_box(0));
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; 
lean_dec_ref(v___x_1556_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
return v_a_1558_;
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1587_; 
v_a_1559_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1561_ = v___x_1557_;
v_isShared_1562_ = v_isSharedCheck_1587_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1587_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1563_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1564_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1565_ = lean_unsigned_to_nat(89u);
v___x_1566_ = lean_unsigned_to_nat(4u);
v___x_1567_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1570_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1569_, v_noBuild_1515_);
v___x_1571_ = lean_string_append(v___x_1567_, v___x_1570_);
lean_dec_ref(v___x_1570_);
v___x_1572_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1573_ = lean_string_append(v___x_1571_, v___x_1572_);
v___x_1574_ = lean_io_error_to_string(v_a_1559_);
v___x_1575_ = lean_string_append(v___x_1573_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1577_ = lean_string_append(v___x_1575_, v___x_1576_);
v___x_1578_ = l_String_quote(v___x_1556_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 3);
lean_ctor_set(v___x_1561_, 0, v___x_1578_);
v___x_1580_ = v___x_1561_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1581_ = l_Std_Format_defWidth;
v___x_1582_ = l_Std_Format_pretty(v___x_1580_, v___x_1581_, v___x_1568_, v___x_1568_);
v___x_1583_ = lean_string_append(v___x_1577_, v___x_1582_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = l_mkPanicMessageWithDecl(v___x_1563_, v___x_1564_, v___x_1565_, v___x_1566_, v___x_1583_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1584_);
return v___x_1585_;
}
}
}
}
}
v___jp_1590_:
{
if (v___y_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_dec(v_numJobs_1589_);
lean_dec_ref(v_out_1509_);
v___x_1592_ = lean_box(0);
return v___x_1592_;
}
else
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_nat_dec_eq(v_numJobs_1589_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_nat_dec_eq(v_numJobs_1589_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = l_Nat_reprFast(v_numJobs_1589_);
v___x_1598_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
v___x_1599_ = lean_string_append(v___x_1597_, v___x_1598_);
v___y_1513_ = v___y_1591_;
v___y_1514_ = v___x_1599_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1600_; 
lean_dec(v_numJobs_1589_);
v___x_1600_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
v___y_1513_ = v___y_1591_;
v___y_1514_ = v___x_1600_;
goto v___jp_1512_;
}
}
else
{
lean_object* v_putStr_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_numJobs_1589_);
v_putStr_1601_ = lean_ctor_get(v_out_1509_, 4);
lean_inc_ref(v_putStr_1601_);
lean_dec_ref(v_out_1509_);
v___x_1602_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
v___x_1603_ = lean_apply_2(v_putStr_1601_, v___x_1602_, lean_box(0));
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
return v_a_1604_;
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_a_1605_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1606_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_1607_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_1608_ = lean_unsigned_to_nat(89u);
v___x_1609_ = lean_unsigned_to_nat(4u);
v___x_1610_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_1611_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_1612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1611_, v___x_1594_);
v___x_1613_ = lean_string_append(v___x_1610_, v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
v___x_1616_ = lean_io_error_to_string(v_a_1605_);
v___x_1617_ = lean_string_append(v___x_1615_, v___x_1616_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_1619_ = lean_string_append(v___x_1617_, v___x_1618_);
v___x_1620_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
v___x_1622_ = l_mkPanicMessageWithDecl(v___x_1606_, v___x_1607_, v___x_1608_, v___x_1609_, v___x_1621_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_1622_);
return v___x_1623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* v_cfg_1663_, lean_object* v_out_1664_, lean_object* v_result_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_1663_, v_out_1664_, v_result_1665_);
lean_dec_ref(v_cfg_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* v_self_1668_){
_start:
{
lean_object* v_toMonitorResult_1669_; 
v_toMonitorResult_1669_ = lean_ctor_get(v_self_1668_, 0);
lean_inc_ref(v_toMonitorResult_1669_);
return v_toMonitorResult_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* v_self_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(v_self_1670_);
lean_dec_ref(v_self_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* v_00_u03b1_1673_){
_start:
{
lean_object* v___f_1674_; 
v___f_1674_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return v___f_1674_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* v_self_1675_){
_start:
{
lean_object* v_out_1676_; 
v_out_1676_ = lean_ctor_get(v_self_1675_, 1);
if (lean_obj_tag(v_out_1676_) == 0)
{
uint8_t v___x_1677_; 
v___x_1677_ = 0;
return v___x_1677_;
}
else
{
uint8_t v___x_1678_; 
v___x_1678_ = 1;
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* v_self_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_1679_);
lean_dec_ref(v_self_1679_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* v_00_u03b1_1682_, lean_object* v_self_1683_){
_start:
{
lean_object* v_out_1684_; 
v_out_1684_ = lean_ctor_get(v_self_1683_, 1);
if (lean_obj_tag(v_out_1684_) == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = 0;
return v___x_1685_;
}
else
{
uint8_t v___x_1686_; 
v___x_1686_ = 1;
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* v_00_u03b1_1687_, lean_object* v_self_1688_){
_start:
{
uint8_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_1687_, v_self_1688_);
lean_dec_ref(v_self_1688_);
v_r_1690_ = lean_box(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* v_ctx_1699_, lean_object* v_job_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_failures_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
lean_inc_ref(v_job_1700_);
v___x_1702_ = l_Lake_Job_toOpaque___redArg(v_job_1700_);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_mk_empty_array_with_capacity(v___x_1703_);
v___x_1705_ = lean_array_push(v___x_1704_, v___x_1702_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
v___x_1708_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
v___x_1709_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(v_ctx_1699_, v___x_1705_, v___x_1707_, v___x_1708_);
v_failures_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_failures_1710_);
v___x_1711_ = lean_array_get_size(v_failures_1710_);
lean_dec_ref(v_failures_1710_);
v___x_1712_ = lean_nat_dec_eq(v___x_1711_, v___x_1706_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v_job_1700_);
v___x_1713_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1709_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
return v___x_1714_;
}
else
{
lean_object* v_task_1715_; lean_object* v___x_1716_; 
v_task_1715_ = lean_ctor_get(v_job_1700_, 0);
lean_inc_ref(v_task_1715_);
lean_dec_ref(v_job_1700_);
v___x_1716_ = lean_io_wait(v_task_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1716_, 1);
lean_dec(v_unused_1726_);
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1721_);
lean_ctor_set(v___x_1719_, 0, v___x_1709_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; lean_object* v_unused_1736_; 
v_unused_1735_ = lean_ctor_get(v___x_1716_, 1);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v___x_1716_, 0);
lean_dec(v_unused_1736_);
v___x_1728_ = v___x_1716_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v___x_1716_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 0);
lean_ctor_set(v___x_1728_, 1, v___x_1730_);
lean_ctor_set(v___x_1728_, 0, v___x_1709_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* v_ctx_1737_, lean_object* v_job_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1737_, v_job_1738_);
lean_dec_ref(v_ctx_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* v_00_u03b1_1741_, lean_object* v_ctx_1742_, lean_object* v_job_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_1742_, v_job_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_ctx_1747_, lean_object* v_job_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_1746_, v_ctx_1747_, v_job_1748_);
lean_dec_ref(v_ctx_1747_);
return v_res_1750_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_unsigned_to_nat(16u);
v___x_1755_ = lean_mk_array(v___x_1754_, v___x_1753_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1);
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* v_ws_1761_, lean_object* v_cfg_1762_, lean_object* v_jobs_1763_){
_start:
{
uint8_t v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v_val_1775_; lean_object* v_val_1789_; uint8_t v___x_1809_; 
v___x_1809_ = l_System_Platform_isOSX;
if (v___x_1809_ == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_1810_; 
v_macosxDeploymentTarget_x3f_1810_ = lean_ctor_get(v_cfg_1762_, 3);
lean_inc(v_macosxDeploymentTarget_x3f_1810_);
v_val_1789_ = v_macosxDeploymentTarget_x3f_1810_;
goto v___jp_1788_;
}
else
{
lean_object* v_macosxDeploymentTarget_x3f_1811_; 
v_macosxDeploymentTarget_x3f_1811_ = lean_ctor_get(v_cfg_1762_, 3);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_1811_) == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___y_1815_; 
v___x_1812_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__3));
v___x_1813_ = lean_io_getenv(v___x_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__4));
v___y_1815_ = v___x_1817_;
goto v___jp_1814_;
}
else
{
lean_object* v_val_1818_; 
v_val_1818_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_val_1818_);
lean_dec_ref_known(v___x_1813_, 1);
v___y_1815_ = v_val_1818_;
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1815_);
v_val_1789_ = v___x_1816_;
goto v___jp_1788_;
}
}
else
{
lean_inc_ref(v_macosxDeploymentTarget_x3f_1811_);
v_val_1789_ = v_macosxDeploymentTarget_x3f_1811_;
goto v___jp_1788_;
}
}
v___jp_1765_:
{
lean_object* v_lakeEnv_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint64_t v___x_1779_; uint64_t v___x_1780_; uint64_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_lakeEnv_1776_ = lean_ctor_get(v_ws_1761_, 0);
v___x_1777_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v___x_1777_, 0, v___y_1771_);
lean_ctor_set(v___x_1777_, 1, v___y_1773_);
lean_ctor_set(v___x_1777_, 2, v___y_1770_);
lean_ctor_set(v___x_1777_, 3, v___y_1767_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*4, v___y_1769_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*4 + 1, v___y_1774_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*4 + 2, v___y_1766_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*4 + 3, v___y_1768_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*4 + 4, v___y_1772_);
v___x_1778_ = l_Lake_Env_leanGithash(v_lakeEnv_1776_);
v___x_1779_ = l_Lake_Hash_nil;
v___x_1780_ = lean_string_hash(v___x_1778_);
v___x_1781_ = lean_uint64_mix_hash(v___x_1779_, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
v___x_1783_ = lean_string_append(v___x_1782_, v___x_1778_);
lean_dec_ref(v___x_1778_);
v___x_1784_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
v___x_1785_ = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
v___x_1786_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1786_, 0, v___x_1783_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
lean_ctor_set(v___x_1786_, 2, v___x_1785_);
lean_ctor_set_uint64(v___x_1786_, sizeof(void*)*3, v___x_1781_);
v___x_1787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1777_);
lean_ctor_set(v___x_1787_, 1, v_ws_1761_);
lean_ctor_set(v___x_1787_, 2, v___x_1786_);
lean_ctor_set(v___x_1787_, 3, v_jobs_1763_);
lean_ctor_set(v___x_1787_, 4, v_val_1775_);
return v___x_1787_;
}
v___jp_1788_:
{
lean_object* v_outputsFile_x3f_1790_; 
v_outputsFile_x3f_1790_ = lean_ctor_get(v_cfg_1762_, 1);
lean_inc(v_outputsFile_x3f_1790_);
if (lean_obj_tag(v_outputsFile_x3f_1790_) == 0)
{
lean_object* v_toLogConfig_1791_; uint8_t v_oldMode_1792_; uint8_t v_trustHash_1793_; uint8_t v_noBuild_1794_; uint8_t v_verbosity_1795_; uint8_t v_showSuccess_1796_; lean_object* v_leanOptOverrides_1797_; lean_object* v___x_1798_; 
v_toLogConfig_1791_ = lean_ctor_get(v_cfg_1762_, 0);
lean_inc_ref(v_toLogConfig_1791_);
v_oldMode_1792_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4);
v_trustHash_1793_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 1);
v_noBuild_1794_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 2);
v_verbosity_1795_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 3);
v_showSuccess_1796_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 4);
v_leanOptOverrides_1797_ = lean_ctor_get(v_cfg_1762_, 2);
lean_inc(v_leanOptOverrides_1797_);
lean_dec_ref(v_cfg_1762_);
v___x_1798_ = lean_box(0);
v___y_1766_ = v_noBuild_1794_;
v___y_1767_ = v_val_1789_;
v___y_1768_ = v_verbosity_1795_;
v___y_1769_ = v_oldMode_1792_;
v___y_1770_ = v_leanOptOverrides_1797_;
v___y_1771_ = v_toLogConfig_1791_;
v___y_1772_ = v_showSuccess_1796_;
v___y_1773_ = v_outputsFile_x3f_1790_;
v___y_1774_ = v_trustHash_1793_;
v_val_1775_ = v___x_1798_;
goto v___jp_1765_;
}
else
{
lean_object* v_toLogConfig_1799_; uint8_t v_oldMode_1800_; uint8_t v_trustHash_1801_; uint8_t v_noBuild_1802_; uint8_t v_verbosity_1803_; uint8_t v_showSuccess_1804_; lean_object* v_leanOptOverrides_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_toLogConfig_1799_ = lean_ctor_get(v_cfg_1762_, 0);
lean_inc_ref(v_toLogConfig_1799_);
v_oldMode_1800_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4);
v_trustHash_1801_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 1);
v_noBuild_1802_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 2);
v_verbosity_1803_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 3);
v_showSuccess_1804_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*4 + 4);
v_leanOptOverrides_1805_ = lean_ctor_get(v_cfg_1762_, 2);
lean_inc(v_leanOptOverrides_1805_);
lean_dec_ref(v_cfg_1762_);
v___x_1806_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2, &l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2);
v___x_1807_ = lean_st_mk_ref(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___y_1766_ = v_noBuild_1802_;
v___y_1767_ = v_val_1789_;
v___y_1768_ = v_verbosity_1803_;
v___y_1769_ = v_oldMode_1800_;
v___y_1770_ = v_leanOptOverrides_1805_;
v___y_1771_ = v_toLogConfig_1799_;
v___y_1772_ = v_showSuccess_1804_;
v___y_1773_ = v_outputsFile_x3f_1790_;
v___y_1774_ = v_trustHash_1801_;
v_val_1775_ = v___x_1808_;
goto v___jp_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(lean_object* v_ws_1819_, lean_object* v_cfg_1820_, lean_object* v_jobs_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_1819_, v_cfg_1820_, v_jobs_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* v_build_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_log_1832_; uint8_t v_action_1833_; uint8_t v_wantsRebuild_1834_; lean_object* v_trace_1835_; lean_object* v_buildTime_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1865_; 
v_log_1832_ = lean_ctor_get(v___y_1830_, 0);
v_action_1833_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3);
v_wantsRebuild_1834_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 1);
v_trace_1835_ = lean_ctor_get(v___y_1830_, 1);
v_buildTime_1836_ = lean_ctor_get(v___y_1830_, 2);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___y_1830_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1838_ = v___y_1830_;
v_isShared_1839_ = v_isSharedCheck_1865_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_buildTime_1836_);
lean_inc(v_trace_1835_);
lean_inc(v_log_1832_);
lean_dec(v___y_1830_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1865_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_apply_7(v_build_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v_log_1832_, lean_box(0));
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_a_1842_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1844_ = v___x_1840_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1842_);
v___x_1847_ = v___x_1838_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1842_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_trace_1835_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_buildTime_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*3, v_action_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*3 + 1, v_wantsRebuild_1834_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v___x_1847_);
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1841_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1864_; 
v_a_1853_ = lean_ctor_get(v___x_1840_, 0);
v_a_1854_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1856_ = v___x_1840_;
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_inc(v_a_1853_);
lean_dec(v___x_1840_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1854_);
v___x_1859_ = v___x_1838_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1854_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_trace_1835_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_buildTime_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*3, v_action_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*3 + 1, v_wantsRebuild_1834_);
v___x_1859_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v___x_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1853_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* v_build_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(v_build_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* v_bctx_1876_, lean_object* v_build_1877_, lean_object* v_caption_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___f_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1880_ = lean_box(1);
v___x_1881_ = lean_st_mk_ref(v___x_1880_);
v___f_1882_ = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1882_, 0, v_build_1877_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_unsigned_to_nat(0u);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_box(0);
v___x_1887_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
v___x_1888_ = l_Lake_Job_async___redArg(v___x_1883_, v___f_1882_, v___x_1884_, v_caption_1878_, v___x_1887_, v___x_1886_, v___x_1885_, v___x_1881_, v_bctx_1876_);
v___x_1889_ = lean_st_ref_get(v___x_1881_);
lean_dec(v___x_1881_);
lean_dec(v___x_1889_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* v_bctx_1890_, lean_object* v_build_1891_, lean_object* v_caption_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1890_, v_build_1891_, v_caption_1892_);
lean_dec_ref(v_bctx_1890_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* v_00_u03b1_1895_, lean_object* v_bctx_1896_, lean_object* v_build_1897_, lean_object* v_caption_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v_bctx_1896_, v_build_1897_, v_caption_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_bctx_1902_, lean_object* v_build_1903_, lean_object* v_caption_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(v_00_u03b1_1901_, v_bctx_1902_, v_build_1903_, v_caption_1904_);
lean_dec_ref(v_bctx_1902_);
return v_res_1906_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
if (lean_obj_tag(v_x_1908_) == 0)
{
uint8_t v___x_1909_; 
v___x_1909_ = 1;
return v___x_1909_;
}
else
{
uint8_t v___x_1910_; 
v___x_1910_ = 0;
return v___x_1910_;
}
}
else
{
if (lean_obj_tag(v_x_1908_) == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = 0;
return v___x_1911_;
}
else
{
lean_object* v_val_1912_; uint8_t v___x_1913_; 
v_val_1912_ = lean_ctor_get(v_x_1908_, 0);
v___x_1913_ = lean_unbox(v_val_1912_);
if (v___x_1913_ == 0)
{
lean_object* v_val_1914_; uint8_t v___x_1915_; 
v_val_1914_ = lean_ctor_get(v_x_1907_, 0);
v___x_1915_ = lean_unbox(v_val_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; 
v___x_1916_ = 1;
return v___x_1916_;
}
else
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_unbox(v_val_1912_);
return v___x_1917_;
}
}
else
{
lean_object* v_val_1918_; uint8_t v___x_1919_; 
v_val_1918_ = lean_ctor_get(v_x_1907_, 0);
v___x_1919_ = lean_unbox(v_val_1918_);
return v___x_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_1920_, v_x_1921_);
lean_dec(v_x_1921_);
lean_dec(v_x_1920_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(lean_object* v___x_1924_, uint8_t v___x_1925_, uint8_t v___x_1926_, lean_object* v_as_1927_, size_t v_i_1928_, size_t v_stop_1929_, lean_object* v_b_1930_){
_start:
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_usize_dec_eq(v_i_1928_, v_stop_1929_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; size_t v___x_1935_; size_t v___x_1936_; 
v___x_1933_ = lean_array_uget_borrowed(v_as_1927_, v_i_1928_);
lean_inc_ref(v___x_1924_);
v___x_1934_ = l_Lake_logToStream(v___x_1933_, v___x_1924_, v___x_1925_, v___x_1926_);
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = lean_usize_add(v_i_1928_, v___x_1935_);
v_i_1928_ = v___x_1936_;
v_b_1930_ = v___x_1934_;
goto _start;
}
else
{
lean_dec_ref(v___x_1924_);
return v_b_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(lean_object* v___x_1938_, lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_as_1941_, lean_object* v_i_1942_, lean_object* v_stop_1943_, lean_object* v_b_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_1007__boxed_1946_; uint8_t v___x_1008__boxed_1947_; size_t v_i_boxed_1948_; size_t v_stop_boxed_1949_; lean_object* v_res_1950_; 
v___x_1007__boxed_1946_ = lean_unbox(v___x_1939_);
v___x_1008__boxed_1947_ = lean_unbox(v___x_1940_);
v_i_boxed_1948_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_stop_boxed_1949_ = lean_unbox_usize(v_stop_1943_);
lean_dec(v_stop_1943_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1938_, v___x_1007__boxed_1946_, v___x_1008__boxed_1947_, v_as_1941_, v_i_boxed_1948_, v_stop_boxed_1949_, v_b_1944_);
lean_dec_ref(v_as_1941_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(lean_object* v___x_1951_, uint8_t v___x_1952_, uint8_t v___x_1953_, lean_object* v_ws_1954_, lean_object* v_outputsRef_x3f_1955_, lean_object* v_out_1956_, lean_object* v_outputsFile_1957_, uint8_t v_isVerbose_1958_){
_start:
{
lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1972_; lean_object* v___y_1973_; uint8_t v___x_2055_; 
v___x_2055_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1954_);
if (v___x_2055_ == 0)
{
lean_object* v_packages_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v_baseName_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_packages_2056_ = lean_ctor_get(v_ws_1954_, 4);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = lean_array_fget_borrowed(v_packages_2056_, v___x_2057_);
v_baseName_2059_ = lean_ctor_get(v___x_2058_, 1);
lean_inc(v_baseName_2059_);
v___x_2060_ = l_Lean_Name_toString(v_baseName_2059_, v___x_2055_);
v___x_2061_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__16));
v___x_2062_ = lean_string_append(v___x_2060_, v___x_2061_);
v___x_2063_ = 2;
v___x_2064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*1, v___x_2063_);
lean_inc_ref(v___x_1951_);
v___x_2065_ = l_Lake_logToStream(v___x_2064_, v___x_1951_, v___x_1952_, v___x_1953_);
lean_dec_ref_known(v___x_2064_, 1);
goto v___jp_1981_;
}
else
{
goto v___jp_1981_;
}
v___jp_1960_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_box(0);
return v___x_1961_;
}
v___jp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = lean_array_get_size(v___y_1963_);
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_nat_dec_lt(v___y_1964_, v___x_1965_);
if (v___x_1967_ == 0)
{
lean_dec_ref(v___y_1963_);
lean_dec_ref(v___x_1951_);
return v___x_1966_;
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1965_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1951_, v___x_1952_, v___x_1953_, v___y_1963_, v___x_1968_, v___x_1969_, v___x_1966_);
lean_dec_ref(v___y_1963_);
return v___x_1970_;
}
}
v___jp_1971_:
{
if (v_isVerbose_1958_ == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___x_1951_);
v___x_1974_ = lean_box(0);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = lean_array_get_size(v___y_1972_);
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_nat_dec_lt(v___y_1973_, v___x_1975_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___x_1951_);
return v___x_1976_;
}
else
{
size_t v___x_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = lean_usize_of_nat(v___x_1975_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_1951_, v___x_1952_, v___x_1953_, v___y_1972_, v___x_1978_, v___x_1979_, v___x_1976_);
lean_dec_ref(v___y_1972_);
return v___x_1980_;
}
}
}
v___jp_1981_:
{
if (lean_obj_tag(v_outputsRef_x3f_1955_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1983_; lean_object* v_packages_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v_config_1987_; lean_object* v_toLeanConfig_1988_; lean_object* v_platformIndependent_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_val_1982_ = lean_ctor_get(v_outputsRef_x3f_1955_, 0);
v___x_1983_ = lean_st_ref_get(v_val_1982_);
v_packages_1984_ = lean_ctor_get(v_ws_1954_, 4);
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_array_fget_borrowed(v_packages_1984_, v___x_1985_);
v_config_1987_ = lean_ctor_get(v___x_1986_, 6);
v_toLeanConfig_1988_ = lean_ctor_get(v_config_1987_, 1);
v_platformIndependent_1989_ = lean_ctor_get(v_toLeanConfig_1988_, 10);
v___x_1990_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2));
v___x_1991_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_1989_, v___x_1990_);
v___x_1992_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3));
v___x_1993_ = l_Lake_CacheMap_writeFile(v_outputsFile_1957_, v___x_1983_, v___x_1991_, v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 2);
v___x_1995_ = lean_array_get_size(v_a_1994_);
v___x_1996_ = lean_nat_dec_eq(v___x_1995_, v___x_1985_);
if (v___x_1996_ == 0)
{
if (v_isVerbose_1958_ == 0)
{
lean_dec(v_a_1994_);
lean_dec_ref(v_out_1956_);
lean_dec_ref(v___x_1951_);
goto v___jp_1960_;
}
else
{
lean_object* v_putStr_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_putStr_1997_ = lean_ctor_get(v_out_1956_, 4);
lean_inc_ref(v_putStr_1997_);
lean_dec_ref(v_out_1956_);
v___x_1998_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4));
v___x_1999_ = lean_apply_2(v_putStr_1997_, v___x_1998_, lean_box(0));
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_dec_ref_known(v___x_1999_, 1);
v___y_1963_ = v_a_1994_;
v___y_1964_ = v___x_1985_;
goto v___jp_1962_;
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2002_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2003_ = lean_unsigned_to_nat(89u);
v___x_2004_ = lean_unsigned_to_nat(4u);
v___x_2005_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
v___x_2006_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
v___x_2007_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2006_, v_isVerbose_1958_);
v___x_2008_ = lean_string_append(v___x_2005_, v___x_2007_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18));
v___x_2010_ = lean_string_append(v___x_2008_, v___x_2009_);
v___x_2011_ = lean_io_error_to_string(v_a_2000_);
v___x_2012_ = lean_string_append(v___x_2010_, v___x_2011_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2014_ = lean_string_append(v___x_2012_, v___x_2013_);
v___x_2015_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
v___x_2016_ = lean_string_append(v___x_2014_, v___x_2015_);
v___x_2017_ = l_mkPanicMessageWithDecl(v___x_2001_, v___x_2002_, v___x_2003_, v___x_2004_, v___x_2016_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2017_);
v___y_1963_ = v_a_1994_;
v___y_1964_ = v___x_1985_;
goto v___jp_1962_;
}
}
}
else
{
lean_dec(v_a_1994_);
lean_dec_ref(v_out_1956_);
lean_dec_ref(v___x_1951_);
goto v___jp_1960_;
}
}
else
{
lean_object* v_a_2019_; lean_object* v_putStr_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_a_2019_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_1993_, 2);
v_putStr_2020_ = lean_ctor_get(v_out_1956_, 4);
lean_inc_ref(v_putStr_2020_);
lean_dec_ref(v_out_1956_);
v___x_2021_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8));
v___x_2022_ = lean_apply_2(v_putStr_2020_, v___x_2021_, lean_box(0));
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref_known(v___x_2022_, 1);
v___y_1972_ = v_a_2019_;
v___y_1973_ = v___x_1985_;
goto v___jp_1971_;
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2025_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2026_ = lean_unsigned_to_nat(89u);
v___x_2027_ = lean_unsigned_to_nat(4u);
v___x_2028_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2029_ = lean_io_error_to_string(v_a_2023_);
v___x_2030_ = lean_string_append(v___x_2028_, v___x_2029_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2032_ = lean_string_append(v___x_2030_, v___x_2031_);
v___x_2033_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
v___x_2034_ = lean_string_append(v___x_2032_, v___x_2033_);
v___x_2035_ = l_mkPanicMessageWithDecl(v___x_2024_, v___x_2025_, v___x_2026_, v___x_2027_, v___x_2034_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2035_);
v___y_1972_ = v_a_2019_;
v___y_1973_ = v___x_1985_;
goto v___jp_1971_;
}
}
}
else
{
lean_object* v_putStr_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v_outputsFile_1957_);
lean_dec_ref(v___x_1951_);
v_putStr_2037_ = lean_ctor_get(v_out_1956_, 4);
lean_inc_ref(v_putStr_2037_);
lean_dec_ref(v_out_1956_);
v___x_2038_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12));
v___x_2039_ = lean_apply_2(v_putStr_2037_, v___x_2038_, lean_box(0));
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
return v_a_2040_;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2041_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2042_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1));
v___x_2043_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
v___x_2044_ = lean_unsigned_to_nat(89u);
v___x_2045_ = lean_unsigned_to_nat(4u);
v___x_2046_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19);
v___x_2047_ = lean_io_error_to_string(v_a_2041_);
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20));
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15);
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
v___x_2053_ = l_mkPanicMessageWithDecl(v___x_2042_, v___x_2043_, v___x_2044_, v___x_2045_, v___x_2052_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2053_);
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(lean_object* v___x_2066_, lean_object* v___x_2067_, lean_object* v___x_2068_, lean_object* v_ws_2069_, lean_object* v_outputsRef_x3f_2070_, lean_object* v_out_2071_, lean_object* v_outputsFile_2072_, lean_object* v_isVerbose_2073_, lean_object* v_a_2074_){
_start:
{
uint8_t v___x_1177__boxed_2075_; uint8_t v___x_1178__boxed_2076_; uint8_t v_isVerbose_boxed_2077_; lean_object* v_res_2078_; 
v___x_1177__boxed_2075_ = lean_unbox(v___x_2067_);
v___x_1178__boxed_2076_ = lean_unbox(v___x_2068_);
v_isVerbose_boxed_2077_ = lean_unbox(v_isVerbose_2073_);
v_res_2078_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_2066_, v___x_1177__boxed_2075_, v___x_1178__boxed_2076_, v_ws_2069_, v_outputsRef_x3f_2070_, v_out_2071_, v_outputsFile_2072_, v_isVerbose_boxed_2077_);
lean_dec(v_outputsRef_x3f_2070_);
lean_dec_ref(v_ws_2069_);
return v_res_2078_;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0(void){
_start:
{
uint32_t v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = 3;
v___x_2080_ = lean_uint32_to_uint8(v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(lean_object* v_cfg_2081_, lean_object* v_bctx_2082_, lean_object* v_mctx_2083_, lean_object* v_result_2084_){
_start:
{
lean_object* v___y_2087_; lean_object* v_out_2090_; uint8_t v_outLv_2091_; uint8_t v_useAnsi_2092_; lean_object* v_toMonitorResult_2093_; lean_object* v_out_2094_; lean_object* v___x_2095_; uint8_t v_noBuild_2096_; uint8_t v_verbosity_2097_; lean_object* v_outputsFile_x3f_2098_; 
v_out_2090_ = lean_ctor_get(v_mctx_2083_, 1);
lean_inc_ref_n(v_out_2090_, 2);
v_outLv_2091_ = lean_ctor_get_uint8(v_mctx_2083_, sizeof(void*)*3);
v_useAnsi_2092_ = lean_ctor_get_uint8(v_mctx_2083_, sizeof(void*)*3 + 4);
lean_dec_ref(v_mctx_2083_);
v_toMonitorResult_2093_ = lean_ctor_get(v_result_2084_, 0);
lean_inc_ref_n(v_toMonitorResult_2093_, 2);
v_out_2094_ = lean_ctor_get(v_result_2084_, 1);
lean_inc_ref(v_out_2094_);
lean_dec_ref(v_result_2084_);
v___x_2095_ = l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_2081_, v_out_2090_, v_toMonitorResult_2093_);
v_noBuild_2096_ = lean_ctor_get_uint8(v_cfg_2081_, sizeof(void*)*4 + 2);
v_verbosity_2097_ = lean_ctor_get_uint8(v_cfg_2081_, sizeof(void*)*4 + 3);
v_outputsFile_x3f_2098_ = lean_ctor_get(v_cfg_2081_, 1);
lean_inc(v_outputsFile_x3f_2098_);
lean_dec_ref(v_cfg_2081_);
if (lean_obj_tag(v_outputsFile_x3f_2098_) == 1)
{
lean_object* v_val_2113_; lean_object* v_toContext_2114_; lean_object* v_outputsRef_x3f_2115_; uint8_t v___y_2117_; 
v_val_2113_ = lean_ctor_get(v_outputsFile_x3f_2098_, 0);
lean_inc(v_val_2113_);
lean_dec_ref_known(v_outputsFile_x3f_2098_, 1);
v_toContext_2114_ = lean_ctor_get(v_bctx_2082_, 1);
v_outputsRef_x3f_2115_ = lean_ctor_get(v_bctx_2082_, 4);
if (v_verbosity_2097_ == 2)
{
uint8_t v___x_2119_; 
v___x_2119_ = 1;
v___y_2117_ = v___x_2119_;
goto v___jp_2116_;
}
else
{
uint8_t v___x_2120_; 
v___x_2120_ = 0;
v___y_2117_ = v___x_2120_;
goto v___jp_2116_;
}
v___jp_2116_:
{
lean_object* v___x_2118_; 
lean_inc_ref(v_out_2090_);
v___x_2118_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_2090_, v_outLv_2091_, v_useAnsi_2092_, v_toContext_2114_, v_outputsRef_x3f_2115_, v_out_2090_, v_val_2113_, v___y_2117_);
goto v___jp_2099_;
}
}
else
{
lean_dec(v_outputsFile_x3f_2098_);
lean_dec_ref(v_out_2090_);
goto v___jp_2099_;
}
v___jp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_mk_io_user_error(v___y_2087_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
v___jp_2099_:
{
if (lean_obj_tag(v_out_2094_) == 0)
{
if (v_noBuild_2096_ == 0)
{
lean_object* v_a_2100_; 
lean_dec_ref(v_toMonitorResult_2093_);
v_a_2100_ = lean_ctor_get(v_out_2094_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v_out_2094_, 1);
v___y_2087_ = v_a_2100_;
goto v___jp_2086_;
}
else
{
uint8_t v_wantsRebuild_2101_; 
v_wantsRebuild_2101_ = lean_ctor_get_uint8(v_toMonitorResult_2093_, sizeof(void*)*2);
lean_dec_ref(v_toMonitorResult_2093_);
if (v_wantsRebuild_2101_ == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v_out_2094_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v_out_2094_, 1);
v___y_2087_ = v_a_2102_;
goto v___jp_2086_;
}
else
{
uint8_t v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref_known(v_out_2094_, 1);
v___x_2103_ = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
v___x_2104_ = lean_io_exit(v___x_2103_);
return v___x_2104_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_toMonitorResult_2093_);
v_a_2105_ = lean_ctor_get(v_out_2094_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_out_2094_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v_out_2094_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v_out_2094_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 0);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(lean_object* v_cfg_2121_, lean_object* v_bctx_2122_, lean_object* v_mctx_2123_, lean_object* v_result_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2121_, v_bctx_2122_, v_mctx_2123_, v_result_2124_);
lean_dec_ref(v_bctx_2122_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild(lean_object* v_00_u03b1_2127_, lean_object* v_cfg_2128_, lean_object* v_bctx_2129_, lean_object* v_mctx_2130_, lean_object* v_result_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2128_, v_bctx_2129_, v_mctx_2130_, v_result_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_cfg_2135_, lean_object* v_bctx_2136_, lean_object* v_mctx_2137_, lean_object* v_result_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(v_00_u03b1_2134_, v_cfg_2135_, v_bctx_2136_, v_mctx_2137_, v_result_2138_);
lean_dec_ref(v_bctx_2136_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* v_ws_2141_, lean_object* v_build_2142_, lean_object* v_cfg_2143_, lean_object* v_caption_2144_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2146_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2147_ = lean_st_mk_ref(v___x_2146_);
lean_inc(v___x_2147_);
v___x_2148_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2143_, v___x_2147_);
lean_inc_ref(v_cfg_2143_);
v___x_2149_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2141_, v_cfg_2143_, v___x_2147_);
v___x_2150_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2149_, v_build_2142_, v_caption_2144_);
v___x_2151_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_2148_, v___x_2150_);
v___x_2152_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2143_, v___x_2149_, v___x_2148_, v___x_2151_);
lean_dec_ref(v___x_2149_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* v_ws_2153_, lean_object* v_build_2154_, lean_object* v_cfg_2155_, lean_object* v_caption_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2153_, v_build_2154_, v_cfg_2155_, v_caption_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* v_00_u03b1_2159_, lean_object* v_ws_2160_, lean_object* v_build_2161_, lean_object* v_cfg_2162_, lean_object* v_caption_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lake_Workspace_runFetchM___redArg(v_ws_2160_, v_build_2161_, v_cfg_2162_, v_caption_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* v_00_u03b1_2166_, lean_object* v_ws_2167_, lean_object* v_build_2168_, lean_object* v_cfg_2169_, lean_object* v_caption_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lake_Workspace_runFetchM(v_00_u03b1_2166_, v_ws_2167_, v_build_2168_, v_cfg_2169_, v_caption_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* v_mctx_2176_, lean_object* v_job_2177_){
_start:
{
lean_object* v___x_2179_; lean_object* v_out_2180_; 
v___x_2179_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_mctx_2176_, v_job_2177_);
v_out_2180_ = lean_ctor_get(v___x_2179_, 1);
lean_inc_ref(v_out_2180_);
if (lean_obj_tag(v_out_2180_) == 0)
{
lean_object* v_toMonitorResult_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2196_; 
v_toMonitorResult_2181_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v___x_2179_, 1);
lean_dec(v_unused_2197_);
v___x_2183_ = v___x_2179_;
v_isShared_2184_ = v_isSharedCheck_2196_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_toMonitorResult_2181_);
lean_dec(v___x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2196_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2195_; 
v_a_2185_ = lean_ctor_get(v_out_2180_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_out_2180_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2187_ = v_out_2180_;
v_isShared_2188_ = v_isSharedCheck_2195_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v_out_2180_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2195_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v___x_2190_);
v___x_2192_ = v___x_2183_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_toMonitorResult_2181_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2221_; 
v_a_2198_ = lean_ctor_get(v_out_2180_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_out_2180_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2200_ = v_out_2180_;
v_isShared_2201_ = v_isSharedCheck_2221_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v_out_2180_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2221_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_toMonitorResult_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2219_; 
v_toMonitorResult_2202_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v___x_2179_, 1);
lean_dec(v_unused_2220_);
v___x_2204_ = v___x_2179_;
v_isShared_2205_ = v_isSharedCheck_2219_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_toMonitorResult_2202_);
lean_dec(v___x_2179_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2219_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_task_2206_; lean_object* v___x_2207_; 
v_task_2206_ = lean_ctor_get(v_a_2198_, 0);
lean_inc_ref(v_task_2206_);
lean_dec(v_a_2198_);
v___x_2207_ = lean_io_wait(v_task_2206_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 2);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_a_2208_);
v___x_2210_ = v___x_2200_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2210_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2210_);
v___x_2212_ = v___x_2204_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_toMonitorResult_2202_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec_ref_known(v___x_2207_, 2);
lean_del_object(v___x_2200_);
v___x_2215_ = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2215_);
v___x_2217_ = v___x_2204_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_toMonitorResult_2202_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* v_mctx_2222_, lean_object* v_job_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2222_, v_job_2223_);
lean_dec_ref(v_mctx_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* v_00_u03b1_2226_, lean_object* v_mctx_2227_, lean_object* v_job_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_2227_, v_job_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_mctx_2232_, lean_object* v_job_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(v_00_u03b1_2231_, v_mctx_2232_, v_job_2233_);
lean_dec_ref(v_mctx_2232_);
return v_res_2235_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* v_ws_2249_, lean_object* v_build_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_out_2262_; 
v___x_2252_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2253_ = lean_st_mk_ref(v___x_2252_);
v___x_2254_ = 0;
v___x_2255_ = 1;
v___x_2256_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(v___x_2253_);
v___x_2257_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_2256_, v___x_2253_);
v___x_2258_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2249_, v___x_2256_, v___x_2253_);
v___x_2259_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2260_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2258_, v_build_2250_, v___x_2259_);
lean_dec_ref(v___x_2258_);
v___x_2261_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2257_, v___x_2260_);
lean_dec_ref(v___x_2257_);
v_out_2262_ = lean_ctor_get(v___x_2261_, 1);
lean_inc_ref(v_out_2262_);
lean_dec_ref(v___x_2261_);
if (lean_obj_tag(v_out_2262_) == 0)
{
lean_dec_ref_known(v_out_2262_, 1);
return v___x_2254_;
}
else
{
lean_dec_ref_known(v_out_2262_, 1);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* v_ws_2263_, lean_object* v_build_2264_, lean_object* v_a_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2263_, v_build_2264_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* v_00_u03b1_2268_, lean_object* v_ws_2269_, lean_object* v_build_2270_){
_start:
{
uint8_t v___x_2272_; 
v___x_2272_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_2269_, v_build_2270_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* v_00_u03b1_2273_, lean_object* v_ws_2274_, lean_object* v_build_2275_, lean_object* v_a_2276_){
_start:
{
uint8_t v_res_2277_; lean_object* v_r_2278_; 
v_res_2277_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_2273_, v_ws_2274_, v_build_2275_);
v_r_2278_ = lean_box(v_res_2277_);
return v_r_2278_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* v_ws_2279_, lean_object* v_build_2280_, lean_object* v_cfg_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2283_ = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
v___x_2284_ = lean_st_mk_ref(v___x_2283_);
lean_inc(v___x_2284_);
v___x_2285_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_2281_, v___x_2284_);
lean_inc_ref(v_cfg_2281_);
v___x_2286_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_2279_, v_cfg_2281_, v___x_2284_);
v___x_2287_ = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
v___x_2288_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(v___x_2286_, v_build_2280_, v___x_2287_);
v___x_2289_ = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_2285_, v___x_2288_);
v___x_2290_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(v_cfg_2281_, v___x_2286_, v___x_2285_, v___x_2289_);
lean_dec_ref(v___x_2286_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* v_ws_2291_, lean_object* v_build_2292_, lean_object* v_cfg_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lake_Workspace_runBuild___redArg(v_ws_2291_, v_build_2292_, v_cfg_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* v_00_u03b1_2296_, lean_object* v_ws_2297_, lean_object* v_build_2298_, lean_object* v_cfg_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lake_Workspace_runBuild___redArg(v_ws_2297_, v_build_2298_, v_cfg_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_ws_2303_, lean_object* v_build_2304_, lean_object* v_cfg_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lake_Workspace_runBuild(v_00_u03b1_2302_, v_ws_2303_, v_build_2304_, v_cfg_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* v_build_2308_, lean_object* v_cfg_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
lean_inc(v_a_2310_);
v___x_2312_ = l_Lake_Workspace_runBuild___redArg(v_a_2310_, v_build_2308_, v_cfg_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* v_build_2313_, lean_object* v_cfg_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lake_runBuild___redArg(v_build_2313_, v_cfg_2314_, v_a_2315_);
lean_dec(v_a_2315_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* v_00_u03b1_2318_, lean_object* v_build_2319_, lean_object* v_cfg_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2323_; 
lean_inc(v_a_2321_);
v___x_2323_ = l_Lake_Workspace_runBuild___redArg(v_a_2321_, v_build_2319_, v_cfg_2320_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* v_00_u03b1_2324_, lean_object* v_build_2325_, lean_object* v_cfg_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lake_runBuild(v_00_u03b1_2324_, v_build_2325_, v_cfg_2326_, v_a_2327_);
lean_dec(v_a_2327_);
return v_res_2329_;
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
