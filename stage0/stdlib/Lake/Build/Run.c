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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__0;
static const lean_string_object l_Lake_mkBuildContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Lean "};
static const lean_object* l_Lake_mkBuildContext___closed__1 = (const lean_object*)&l_Lake_mkBuildContext___closed__1_value;
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__2;
static const lean_string_object l_Lake_mkBuildContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l_Lake_mkBuildContext___closed__3 = (const lean_object*)&l_Lake_mkBuildContext___closed__3_value;
static lean_object* l_Lake_mkBuildContext___closed__4;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_mkBuildContext___closed__5;
static lean_object* l_Lake_mkBuildContext___closed__6;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\x1b[2K\r"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Run_0__Lake_Ansi_resetLine = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Build.Run"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "_private.Lake.Build.Run.0.Lake.print!"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__6 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__7 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__8 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Build"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value),LEAN_SCALAR_PTR_LITERAL(2, 137, 78, 165, 26, 100, 189, 141)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__10 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Run"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__11 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 210, 138, 215, 143, 190, 184, 44)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__12 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(223, 16, 116, 91, 164, 49, 31, 222)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__13 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 129, 2, 182, 107, 115, 87, 113)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__14 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "print!"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__15 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value),((lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value),LEAN_SCALAR_PTR_LITERAL(171, 56, 2, 158, 131, 186, 32, 163)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__16 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " failed: "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__19 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_value;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__21 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__21_value;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
uint32_t l_Lake_LogLevel_icon(uint8_t);
uint8_t l_Lake_instOrdJobAction_ord(uint8_t, uint8_t);
uint8_t lean_strict_and(uint8_t, uint8_t);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_value;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = ": the artifact cache is not enabled for this package, so the artifacts described by the mappings produced by `-o` will not necessarily be available in the cache."};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_value;
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__6;
static lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___closed__7;
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
static lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0;
static lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "build failed"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "uncaught top-level build failure (this is likely a bug in Lake)"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value;
static const lean_ctor_object l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value)}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__5_value;
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_io_wait(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value;
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static uint8_t l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0;
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_exit(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_mkBuildContext___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore;
x_2 = ((lean_object*)(l_Lake_mkBuildContext___closed__1));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_mkBuildContext___closed__3));
x_2 = l_Lake_mkBuildContext___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__6() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_mkBuildContext___closed__5;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lake_mkBuildContext___closed__0;
x_5 = lean_st_mk_ref(x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lake_Env_leanGithash(x_6);
x_8 = l_Lake_Hash_nil;
x_9 = lean_string_hash(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lake_mkBuildContext___closed__4;
x_12 = lean_string_append(x_11, x_7);
lean_dec_ref(x_7);
x_13 = l_Lake_mkBuildContext___closed__6;
x_14 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint64(x_14, sizeof(void*)*3, x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_mkBuildContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_mkBuildContext(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10494;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10487;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10479;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10463;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10367;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10431;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10491;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10493;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7;
x_2 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(x_1, x_6, x_7, x_4);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 4);
lean_dec_ref(x_1);
x_5 = lean_box(x_3);
x_6 = lean_box(x_4);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed), 5, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_3, x_1, x_2, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_4, x_2, x_3, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_MonitorM_run(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_4);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Run_0__Lake_flush(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
x_3 = l_instInhabitedOfMonad___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
x_2 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_2 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_5 = lean_apply_2(x_4, x_2, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_10 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_11 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_12 = lean_unsigned_to_nat(89u);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_16 = lean_io_error_to_string(x_8);
x_17 = lean_string_append(x_15, x_16);
lean_dec_ref(x_16);
x_18 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_19 = lean_string_append(x_17, x_18);
x_20 = l_String_quote(x_2);
lean_ctor_set_tag(x_5, 3);
lean_ctor_set(x_5, 0, x_20);
x_21 = l_Std_Format_defWidth;
x_22 = l_Std_Format_pretty(x_5, x_21, x_14, x_14);
x_23 = lean_string_append(x_19, x_22);
lean_dec_ref(x_22);
x_24 = l_mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_23);
lean_dec_ref(x_23);
x_25 = l_panic___redArg(x_9, x_24);
x_26 = lean_apply_1(x_25, lean_box(0));
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_29 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_30 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_31 = lean_unsigned_to_nat(89u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_35 = lean_io_error_to_string(x_27);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_38 = lean_string_append(x_36, x_37);
x_39 = l_String_quote(x_2);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Std_Format_defWidth;
x_42 = l_Std_Format_pretty(x_40, x_41, x_33, x_33);
x_43 = lean_string_append(x_38, x_42);
lean_dec_ref(x_42);
x_44 = l_mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_43);
lean_dec_ref(x_43);
x_45 = l_panic___redArg(x_28, x_44);
x_46 = lean_apply_1(x_45, lean_box(0));
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_print_x21(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_1);
x_11 = lean_apply_2(x_10, x_1, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_5 = x_12;
x_6 = lean_box(0);
goto block_8;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_16 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_17 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_18 = lean_unsigned_to_nat(89u);
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_22 = lean_io_error_to_string(x_14);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_25 = lean_string_append(x_23, x_24);
x_26 = l_String_quote(x_1);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_26);
x_27 = l_Std_Format_defWidth;
x_28 = l_Std_Format_pretty(x_11, x_27, x_20, x_20);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = l_mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_29);
lean_dec_ref(x_29);
x_31 = l_panic___redArg(x_15, x_30);
x_32 = lean_apply_1(x_31, lean_box(0));
x_5 = x_32;
x_6 = lean_box(0);
goto block_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
x_34 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_35 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_36 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_37 = lean_unsigned_to_nat(89u);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_41 = lean_io_error_to_string(x_33);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_44 = lean_string_append(x_42, x_43);
x_45 = l_String_quote(x_1);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Std_Format_defWidth;
x_48 = l_Std_Format_pretty(x_46, x_47, x_39, x_39);
x_49 = lean_string_append(x_44, x_48);
lean_dec_ref(x_48);
x_50 = l_mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_49);
lean_dec_ref(x_49);
x_51 = l_panic___redArg(x_34, x_50);
x_52 = lean_apply_1(x_51, lean_box(0));
x_5 = x_52;
x_6 = lean_box(0);
goto block_8;
}
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_print(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_1(x_9, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_4 = x_11;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_4 = x_12;
x_5 = lean_box(0);
goto block_7;
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_Monitor_flush(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 5);
if (x_9 == 0)
{
lean_dec_ref(x_3);
goto block_8;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
if (x_10 == 0)
{
lean_dec_ref(x_3);
goto block_8;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_27; lean_object* x_33; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 5);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_18 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
x_19 = lean_array_fget(x_17, x_15);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Fin_add(x_18, x_15, x_20);
lean_dec(x_15);
x_22 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_4, 5, x_21);
lean_ctor_set(x_4, 3, x_22);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_array_get_size(x_1);
x_98 = lean_nat_dec_lt(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_array_get_size(x_2);
x_100 = lean_nat_sub(x_99, x_20);
x_101 = lean_array_fget_borrowed(x_2, x_100);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 2);
x_103 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
x_104 = lean_string_append(x_103, x_102);
x_33 = x_104;
goto block_95;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_nat_sub(x_97, x_20);
x_106 = lean_array_fget_borrowed(x_1, x_105);
x_107 = lean_ctor_get(x_106, 2);
x_108 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
x_109 = lean_string_append(x_108, x_107);
x_110 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
x_111 = lean_string_append(x_109, x_110);
x_112 = l_Nat_reprFast(x_105);
x_113 = lean_string_append(x_111, x_112);
lean_dec_ref(x_112);
x_114 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
x_115 = lean_string_append(x_113, x_114);
x_33 = x_115;
goto block_95;
}
block_26:
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_16);
x_29 = lean_apply_1(x_28, lean_box(0));
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_23 = x_30;
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_31; 
lean_dec_ref(x_29);
x_31 = lean_box(0);
x_23 = x_31;
x_24 = lean_box(0);
goto block_26;
}
}
block_95:
{
lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_16, 4);
x_35 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_36 = lean_unbox_uint32(x_19);
lean_dec(x_19);
x_37 = lean_string_push(x_35, x_36);
x_38 = lean_string_append(x_14, x_37);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
x_40 = lean_string_append(x_38, x_39);
x_41 = l_Nat_reprFast(x_12);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Nat_reprFast(x_13);
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_33);
lean_dec_ref(x_33);
lean_inc_ref(x_34);
lean_inc_ref(x_49);
x_50 = lean_apply_2(x_34, x_49, lean_box(0));
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
lean_dec_ref(x_49);
x_27 = lean_box(0);
goto block_32;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_54 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_55 = lean_unsigned_to_nat(89u);
x_56 = lean_unsigned_to_nat(4u);
x_57 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_58 = lean_unsigned_to_nat(0u);
x_59 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_60 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_59, x_10);
x_61 = lean_string_append(x_57, x_60);
lean_dec_ref(x_60);
x_62 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_io_error_to_string(x_52);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = lean_string_append(x_65, x_47);
x_67 = l_String_quote(x_49);
lean_ctor_set_tag(x_50, 3);
lean_ctor_set(x_50, 0, x_67);
x_68 = l_Std_Format_defWidth;
x_69 = l_Std_Format_pretty(x_50, x_68, x_58, x_58);
x_70 = lean_string_append(x_66, x_69);
lean_dec_ref(x_69);
x_71 = l_mkPanicMessageWithDecl(x_53, x_54, x_55, x_56, x_70);
lean_dec_ref(x_70);
x_72 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_71);
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_73 = lean_ctor_get(x_50, 0);
lean_inc(x_73);
lean_dec(x_50);
x_74 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_75 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_76 = lean_unsigned_to_nat(89u);
x_77 = lean_unsigned_to_nat(4u);
x_78 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_79 = lean_unsigned_to_nat(0u);
x_80 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_81 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_80, x_10);
x_82 = lean_string_append(x_78, x_81);
lean_dec_ref(x_81);
x_83 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_io_error_to_string(x_73);
x_86 = lean_string_append(x_84, x_85);
lean_dec_ref(x_85);
x_87 = lean_string_append(x_86, x_47);
x_88 = l_String_quote(x_49);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Std_Format_defWidth;
x_91 = l_Std_Format_pretty(x_89, x_90, x_79, x_79);
x_92 = lean_string_append(x_87, x_91);
lean_dec_ref(x_91);
x_93 = l_mkPanicMessageWithDecl(x_74, x_75, x_76, x_77, x_92);
lean_dec_ref(x_92);
x_94 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_93);
x_27 = lean_box(0);
goto block_32;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_135; lean_object* x_141; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_116 = lean_ctor_get(x_4, 0);
x_117 = lean_ctor_get(x_4, 1);
x_118 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_119 = lean_ctor_get(x_4, 2);
x_120 = lean_ctor_get(x_4, 3);
x_121 = lean_ctor_get(x_4, 4);
x_122 = lean_ctor_get(x_4, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_4);
x_123 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_123);
lean_dec_ref(x_3);
x_124 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_125 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0;
x_126 = lean_array_fget(x_124, x_122);
x_127 = lean_unsigned_to_nat(1u);
x_128 = l_Fin_add(x_125, x_122, x_127);
lean_dec(x_122);
x_129 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(x_117);
lean_inc(x_116);
x_130 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_130, 0, x_116);
lean_ctor_set(x_130, 1, x_117);
lean_ctor_set(x_130, 2, x_119);
lean_ctor_set(x_130, 3, x_129);
lean_ctor_set(x_130, 4, x_121);
lean_ctor_set(x_130, 5, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*6, x_118);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_array_get_size(x_1);
x_185 = lean_nat_dec_lt(x_183, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_array_get_size(x_2);
x_187 = lean_nat_sub(x_186, x_127);
x_188 = lean_array_fget_borrowed(x_2, x_187);
lean_dec(x_187);
x_189 = lean_ctor_get(x_188, 2);
x_190 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
x_191 = lean_string_append(x_190, x_189);
x_141 = x_191;
goto block_182;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_192 = lean_nat_sub(x_184, x_127);
x_193 = lean_array_fget_borrowed(x_1, x_192);
x_194 = lean_ctor_get(x_193, 2);
x_195 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
x_196 = lean_string_append(x_195, x_194);
x_197 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
x_198 = lean_string_append(x_196, x_197);
x_199 = l_Nat_reprFast(x_192);
x_200 = lean_string_append(x_198, x_199);
lean_dec_ref(x_199);
x_201 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
x_202 = lean_string_append(x_200, x_201);
x_141 = x_202;
goto block_182;
}
block_134:
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
block_140:
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_136);
lean_dec_ref(x_123);
x_137 = lean_apply_1(x_136, lean_box(0));
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_131 = x_138;
x_132 = lean_box(0);
goto block_134;
}
else
{
lean_object* x_139; 
lean_dec_ref(x_137);
x_139 = lean_box(0);
x_131 = x_139;
x_132 = lean_box(0);
goto block_134;
}
}
block_182:
{
lean_object* x_142; lean_object* x_143; uint32_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_142 = lean_ctor_get(x_123, 4);
x_143 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_144 = lean_unbox_uint32(x_126);
lean_dec(x_126);
x_145 = lean_string_push(x_143, x_144);
x_146 = lean_string_append(x_120, x_145);
lean_dec_ref(x_145);
x_147 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
x_148 = lean_string_append(x_146, x_147);
x_149 = l_Nat_reprFast(x_116);
x_150 = lean_string_append(x_148, x_149);
lean_dec_ref(x_149);
x_151 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
x_152 = lean_string_append(x_150, x_151);
x_153 = l_Nat_reprFast(x_117);
x_154 = lean_string_append(x_152, x_153);
lean_dec_ref(x_153);
x_155 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_156 = lean_string_append(x_154, x_155);
x_157 = lean_string_append(x_156, x_141);
lean_dec_ref(x_141);
lean_inc_ref(x_142);
lean_inc_ref(x_157);
x_158 = lean_apply_2(x_142, x_157, lean_box(0));
if (lean_obj_tag(x_158) == 0)
{
lean_dec_ref(x_158);
lean_dec_ref(x_157);
x_135 = lean_box(0);
goto block_140;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
x_161 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_162 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_163 = lean_unsigned_to_nat(89u);
x_164 = lean_unsigned_to_nat(4u);
x_165 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_166 = lean_unsigned_to_nat(0u);
x_167 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_168 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_167, x_10);
x_169 = lean_string_append(x_165, x_168);
lean_dec_ref(x_168);
x_170 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_171 = lean_string_append(x_169, x_170);
x_172 = lean_io_error_to_string(x_159);
x_173 = lean_string_append(x_171, x_172);
lean_dec_ref(x_172);
x_174 = lean_string_append(x_173, x_155);
x_175 = l_String_quote(x_157);
if (lean_is_scalar(x_160)) {
 x_176 = lean_alloc_ctor(3, 1, 0);
} else {
 x_176 = x_160;
 lean_ctor_set_tag(x_176, 3);
}
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Std_Format_defWidth;
x_178 = l_Std_Format_pretty(x_176, x_177, x_166, x_166);
x_179 = lean_string_append(x_174, x_178);
lean_dec_ref(x_178);
x_180 = l_mkPanicMessageWithDecl(x_161, x_162, x_163, x_164, x_179);
lean_dec_ref(x_179);
x_181 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_180);
x_135 = lean_box(0);
goto block_140;
}
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_1, x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(10000u);
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Nat_reprFast(x_1);
x_7 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0));
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_nat_div(x_1, x_4);
x_10 = l_Nat_reprFast(x_9);
x_11 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_unsigned_to_nat(50u);
x_14 = lean_nat_add(x_1, x_13);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(100u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(10u);
x_18 = lean_nat_mod(x_16, x_17);
lean_dec(x_16);
x_19 = l_Nat_reprFast(x_18);
x_20 = lean_string_append(x_12, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_unsigned_to_nat(1000u);
x_24 = lean_nat_div(x_1, x_23);
lean_dec(x_1);
x_25 = l_Nat_reprFast(x_24);
x_26 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2));
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_5, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_12 = l_Lake_logToStream(x_11, x_1, x_2, x_3);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_5, x_13);
x_5 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_1, x_10, x_11, x_4, x_12, x_13, x_7, x_8);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint32_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; uint32_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; uint32_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_266; lean_object* x_267; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint32_t x_287; lean_object* x_291; uint8_t x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_308; uint8_t x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; uint8_t x_319; uint8_t x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; uint8_t x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; uint8_t x_354; uint8_t x_355; uint8_t x_356; uint8_t x_357; lean_object* x_367; uint8_t x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; uint8_t x_376; uint8_t x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; uint8_t x_388; uint8_t x_389; lean_object* x_395; uint8_t x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; uint8_t x_402; lean_object* x_407; lean_object* x_419; lean_object* x_420; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
x_34 = lean_ctor_get(x_3, 5);
x_35 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_35);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_200 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_201);
x_202 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_419 = lean_task_get_own(x_200);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_407 = x_420;
goto block_418;
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_apply_1(x_19, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_10 = x_16;
x_11 = x_21;
x_12 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_10 = x_16;
x_11 = x_22;
x_12 = lean_box(0);
goto block_14;
}
}
block_27:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_15 = x_24;
x_16 = x_26;
x_17 = lean_box(0);
goto block_23;
}
block_59:
{
uint8_t x_50; 
x_50 = lean_nat_dec_lt(x_48, x_47);
lean_dec(x_48);
if (x_50 == 0)
{
lean_dec(x_47);
lean_dec_ref(x_43);
lean_dec_ref(x_35);
x_15 = x_45;
x_16 = x_44;
x_17 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_box(0);
x_52 = lean_nat_dec_le(x_47, x_47);
if (x_52 == 0)
{
if (x_50 == 0)
{
lean_dec(x_47);
lean_dec_ref(x_43);
lean_dec_ref(x_35);
x_15 = x_45;
x_16 = x_44;
x_17 = lean_box(0);
goto block_23;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_35, x_49, x_40, x_43, x_53, x_54, x_51, x_44);
lean_dec_ref(x_43);
x_24 = x_45;
x_25 = x_55;
goto block_27;
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_35, x_49, x_40, x_43, x_56, x_57, x_51, x_44);
lean_dec_ref(x_43);
x_24 = x_45;
x_25 = x_58;
goto block_27;
}
}
}
block_69:
{
if (x_61 == 0)
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_60);
lean_dec_ref(x_35);
x_15 = x_62;
x_16 = x_63;
x_17 = lean_box(0);
goto block_23;
}
else
{
if (x_66 == 0)
{
x_43 = x_60;
x_44 = x_63;
x_45 = x_62;
x_46 = lean_box(0);
x_47 = x_65;
x_48 = x_64;
x_49 = x_36;
goto block_59;
}
else
{
uint8_t x_68; 
x_68 = 0;
x_43 = x_60;
x_44 = x_63;
x_45 = x_62;
x_46 = lean_box(0);
x_47 = x_65;
x_48 = x_64;
x_49 = x_68;
goto block_59;
}
}
}
block_186:
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_72, 1);
x_82 = lean_ctor_get(x_78, 3);
x_83 = lean_ctor_get(x_81, 4);
x_84 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
lean_ctor_set(x_78, 3, x_84);
x_85 = lean_string_append(x_82, x_79);
lean_dec_ref(x_79);
x_86 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
x_87 = lean_string_append(x_85, x_86);
lean_inc_ref(x_83);
lean_inc_ref(x_87);
x_88 = lean_apply_2(x_83, x_87, lean_box(0));
if (lean_obj_tag(x_88) == 0)
{
lean_dec_ref(x_88);
lean_dec_ref(x_87);
x_60 = x_71;
x_61 = x_73;
x_62 = x_72;
x_63 = x_78;
x_64 = x_75;
x_65 = x_74;
x_66 = x_77;
x_67 = lean_box(0);
goto block_69;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_92 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_93 = lean_unsigned_to_nat(89u);
x_94 = lean_unsigned_to_nat(4u);
x_95 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_96 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7));
x_97 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12));
lean_inc(x_75);
x_98 = l_Lean_Name_num___override(x_97, x_75);
x_99 = l_Lean_Name_str___override(x_98, x_96);
x_100 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
x_101 = l_Lean_Name_str___override(x_99, x_100);
x_102 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_101, x_76);
x_103 = lean_string_append(x_95, x_102);
lean_dec_ref(x_102);
x_104 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_io_error_to_string(x_90);
x_107 = lean_string_append(x_105, x_106);
lean_dec_ref(x_106);
x_108 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_109 = lean_string_append(x_107, x_108);
x_110 = l_String_quote(x_87);
lean_ctor_set_tag(x_88, 3);
lean_ctor_set(x_88, 0, x_110);
x_111 = l_Std_Format_defWidth;
lean_inc_n(x_75, 2);
x_112 = l_Std_Format_pretty(x_88, x_111, x_75, x_75);
x_113 = lean_string_append(x_109, x_112);
lean_dec_ref(x_112);
x_114 = l_mkPanicMessageWithDecl(x_91, x_92, x_93, x_94, x_113);
lean_dec_ref(x_113);
x_115 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_114);
x_60 = x_71;
x_61 = x_73;
x_62 = x_72;
x_63 = x_78;
x_64 = x_75;
x_65 = x_74;
x_66 = x_77;
x_67 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_116 = lean_ctor_get(x_88, 0);
lean_inc(x_116);
lean_dec(x_88);
x_117 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_118 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_119 = lean_unsigned_to_nat(89u);
x_120 = lean_unsigned_to_nat(4u);
x_121 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_122 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7));
x_123 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12));
lean_inc(x_75);
x_124 = l_Lean_Name_num___override(x_123, x_75);
x_125 = l_Lean_Name_str___override(x_124, x_122);
x_126 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
x_127 = l_Lean_Name_str___override(x_125, x_126);
x_128 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_127, x_76);
x_129 = lean_string_append(x_121, x_128);
lean_dec_ref(x_128);
x_130 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_131 = lean_string_append(x_129, x_130);
x_132 = lean_io_error_to_string(x_116);
x_133 = lean_string_append(x_131, x_132);
lean_dec_ref(x_132);
x_134 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_135 = lean_string_append(x_133, x_134);
x_136 = l_String_quote(x_87);
x_137 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Std_Format_defWidth;
lean_inc_n(x_75, 2);
x_139 = l_Std_Format_pretty(x_137, x_138, x_75, x_75);
x_140 = lean_string_append(x_135, x_139);
lean_dec_ref(x_139);
x_141 = l_mkPanicMessageWithDecl(x_117, x_118, x_119, x_120, x_140);
lean_dec_ref(x_140);
x_142 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_141);
x_60 = x_71;
x_61 = x_73;
x_62 = x_72;
x_63 = x_78;
x_64 = x_75;
x_65 = x_74;
x_66 = x_77;
x_67 = lean_box(0);
goto block_69;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_143 = lean_ctor_get(x_72, 1);
x_144 = lean_ctor_get(x_78, 0);
x_145 = lean_ctor_get(x_78, 1);
x_146 = lean_ctor_get_uint8(x_78, sizeof(void*)*6);
x_147 = lean_ctor_get(x_78, 2);
x_148 = lean_ctor_get(x_78, 3);
x_149 = lean_ctor_get(x_78, 4);
x_150 = lean_ctor_get(x_78, 5);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_78);
x_151 = lean_ctor_get(x_143, 4);
x_152 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_153 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_147);
lean_ctor_set(x_153, 3, x_152);
lean_ctor_set(x_153, 4, x_149);
lean_ctor_set(x_153, 5, x_150);
lean_ctor_set_uint8(x_153, sizeof(void*)*6, x_146);
x_154 = lean_string_append(x_148, x_79);
lean_dec_ref(x_79);
x_155 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
x_156 = lean_string_append(x_154, x_155);
lean_inc_ref(x_151);
lean_inc_ref(x_156);
x_157 = lean_apply_2(x_151, x_156, lean_box(0));
if (lean_obj_tag(x_157) == 0)
{
lean_dec_ref(x_157);
lean_dec_ref(x_156);
x_60 = x_71;
x_61 = x_73;
x_62 = x_72;
x_63 = x_153;
x_64 = x_75;
x_65 = x_74;
x_66 = x_77;
x_67 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_161 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_162 = lean_unsigned_to_nat(89u);
x_163 = lean_unsigned_to_nat(4u);
x_164 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_165 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7));
x_166 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12));
lean_inc(x_75);
x_167 = l_Lean_Name_num___override(x_166, x_75);
x_168 = l_Lean_Name_str___override(x_167, x_165);
x_169 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
x_170 = l_Lean_Name_str___override(x_168, x_169);
x_171 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_170, x_76);
x_172 = lean_string_append(x_164, x_171);
lean_dec_ref(x_171);
x_173 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_174 = lean_string_append(x_172, x_173);
x_175 = lean_io_error_to_string(x_158);
x_176 = lean_string_append(x_174, x_175);
lean_dec_ref(x_175);
x_177 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_178 = lean_string_append(x_176, x_177);
x_179 = l_String_quote(x_156);
if (lean_is_scalar(x_159)) {
 x_180 = lean_alloc_ctor(3, 1, 0);
} else {
 x_180 = x_159;
 lean_ctor_set_tag(x_180, 3);
}
lean_ctor_set(x_180, 0, x_179);
x_181 = l_Std_Format_defWidth;
lean_inc_n(x_75, 2);
x_182 = l_Std_Format_pretty(x_180, x_181, x_75, x_75);
x_183 = lean_string_append(x_178, x_182);
lean_dec_ref(x_182);
x_184 = l_mkPanicMessageWithDecl(x_160, x_161, x_162, x_163, x_183);
lean_dec_ref(x_183);
x_185 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_184);
x_60 = x_71;
x_61 = x_73;
x_62 = x_72;
x_63 = x_153;
x_64 = x_75;
x_65 = x_74;
x_66 = x_77;
x_67 = lean_box(0);
goto block_69;
}
}
}
block_199:
{
lean_object* x_198; 
x_198 = l_Lake_Ansi_chalk(x_197, x_193);
lean_dec_ref(x_193);
lean_dec_ref(x_197);
x_70 = lean_box(0);
x_71 = x_188;
x_72 = x_190;
x_73 = x_189;
x_74 = x_192;
x_75 = x_191;
x_76 = x_194;
x_77 = x_195;
x_78 = x_196;
x_79 = x_198;
goto block_186;
}
block_238:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_217 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_218 = lean_string_push(x_217, x_210);
x_219 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
x_220 = lean_string_append(x_218, x_219);
x_221 = l_Nat_reprFast(x_28);
x_222 = lean_string_append(x_220, x_221);
lean_dec_ref(x_221);
x_223 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
x_224 = lean_string_append(x_222, x_223);
x_225 = l_Nat_reprFast(x_29);
x_226 = lean_string_append(x_224, x_225);
lean_dec_ref(x_225);
x_227 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
x_228 = lean_string_append(x_226, x_227);
x_229 = lean_string_append(x_228, x_208);
lean_dec_ref(x_208);
x_230 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
x_231 = lean_string_append(x_229, x_230);
x_232 = lean_string_append(x_231, x_211);
lean_dec_ref(x_211);
x_233 = lean_string_append(x_232, x_230);
x_234 = lean_string_append(x_233, x_201);
lean_dec_ref(x_201);
x_235 = lean_string_append(x_234, x_216);
lean_dec_ref(x_216);
if (x_40 == 0)
{
x_70 = lean_box(0);
x_71 = x_203;
x_72 = x_204;
x_73 = x_214;
x_74 = x_207;
x_75 = x_206;
x_76 = x_209;
x_77 = x_215;
x_78 = x_212;
x_79 = x_235;
goto block_186;
}
else
{
if (x_214 == 0)
{
lean_object* x_236; 
x_236 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
x_187 = lean_box(0);
x_188 = x_203;
x_189 = x_214;
x_190 = x_204;
x_191 = x_206;
x_192 = x_207;
x_193 = x_235;
x_194 = x_209;
x_195 = x_215;
x_196 = x_212;
x_197 = x_236;
goto block_199;
}
else
{
lean_object* x_237; 
x_237 = l_Lake_LogLevel_ansiColor(x_205);
x_187 = lean_box(0);
x_188 = x_203;
x_189 = x_214;
x_190 = x_204;
x_191 = x_206;
x_192 = x_207;
x_193 = x_235;
x_194 = x_209;
x_195 = x_215;
x_196 = x_212;
x_197 = x_237;
goto block_199;
}
}
}
block_253:
{
lean_object* x_252; 
x_252 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_203 = x_239;
x_204 = x_240;
x_205 = x_241;
x_206 = x_242;
x_207 = x_243;
x_208 = x_244;
x_209 = x_245;
x_210 = x_246;
x_211 = x_247;
x_212 = x_248;
x_213 = lean_box(0);
x_214 = x_250;
x_215 = x_251;
x_216 = x_252;
goto block_238;
}
block_274:
{
if (x_42 == 0)
{
lean_dec(x_264);
x_239 = x_254;
x_240 = x_255;
x_241 = x_256;
x_242 = x_257;
x_243 = x_258;
x_244 = x_267;
x_245 = x_259;
x_246 = x_260;
x_247 = x_261;
x_248 = x_262;
x_249 = lean_box(0);
x_250 = x_265;
x_251 = x_266;
goto block_253;
}
else
{
uint8_t x_268; 
x_268 = lean_nat_dec_lt(x_257, x_264);
if (x_268 == 0)
{
lean_dec(x_264);
x_239 = x_254;
x_240 = x_255;
x_241 = x_256;
x_242 = x_257;
x_243 = x_258;
x_244 = x_267;
x_245 = x_259;
x_246 = x_260;
x_247 = x_261;
x_248 = x_262;
x_249 = lean_box(0);
x_250 = x_265;
x_251 = x_266;
goto block_253;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_269 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
x_270 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(x_264);
x_271 = lean_string_append(x_269, x_270);
lean_dec_ref(x_270);
x_272 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
x_273 = lean_string_append(x_271, x_272);
x_203 = x_254;
x_204 = x_255;
x_205 = x_256;
x_206 = x_257;
x_207 = x_258;
x_208 = x_267;
x_209 = x_259;
x_210 = x_260;
x_211 = x_261;
x_212 = x_262;
x_213 = lean_box(0);
x_214 = x_265;
x_215 = x_266;
x_216 = x_273;
goto block_238;
}
}
}
block_290:
{
if (x_202 == 0)
{
lean_object* x_288; 
x_288 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_254 = x_276;
x_255 = x_280;
x_256 = x_279;
x_257 = x_282;
x_258 = x_281;
x_259 = x_283;
x_260 = x_287;
x_261 = x_285;
x_262 = x_286;
x_263 = lean_box(0);
x_264 = x_277;
x_265 = x_278;
x_266 = x_284;
x_267 = x_288;
goto block_274;
}
else
{
lean_object* x_289; 
x_289 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
x_254 = x_276;
x_255 = x_280;
x_256 = x_279;
x_257 = x_282;
x_258 = x_281;
x_259 = x_283;
x_260 = x_287;
x_261 = x_285;
x_262 = x_286;
x_263 = lean_box(0);
x_264 = x_277;
x_265 = x_278;
x_266 = x_284;
x_267 = x_289;
goto block_274;
}
}
block_307:
{
if (x_298 == 0)
{
if (x_41 == 0)
{
lean_dec(x_300);
lean_dec(x_299);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_293);
lean_dec_ref(x_201);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = lean_box(0);
x_6 = x_302;
goto block_9;
}
else
{
if (x_40 == 0)
{
if (x_294 == 0)
{
lean_dec(x_300);
lean_dec(x_299);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_293);
lean_dec_ref(x_201);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = lean_box(0);
x_6 = x_302;
goto block_9;
}
else
{
lean_object* x_303; uint32_t x_304; 
x_303 = l_Lake_JobAction_verb(x_301, x_292);
x_304 = 10004;
x_275 = lean_box(0);
x_276 = x_293;
x_277 = x_295;
x_278 = x_298;
x_279 = x_297;
x_280 = x_296;
x_281 = x_299;
x_282 = x_300;
x_283 = x_294;
x_284 = x_301;
x_285 = x_303;
x_286 = x_302;
x_287 = x_304;
goto block_290;
}
}
else
{
lean_dec(x_300);
lean_dec(x_299);
lean_dec_ref(x_296);
lean_dec(x_295);
lean_dec_ref(x_293);
lean_dec_ref(x_201);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = lean_box(0);
x_6 = x_302;
goto block_9;
}
}
}
else
{
lean_object* x_305; uint32_t x_306; 
x_305 = l_Lake_JobAction_verb(x_301, x_292);
x_306 = l_Lake_LogLevel_icon(x_297);
x_275 = lean_box(0);
x_276 = x_293;
x_277 = x_295;
x_278 = x_298;
x_279 = x_297;
x_280 = x_296;
x_281 = x_299;
x_282 = x_300;
x_283 = x_298;
x_284 = x_301;
x_285 = x_305;
x_286 = x_302;
x_287 = x_306;
goto block_290;
}
}
block_320:
{
if (x_202 == 0)
{
x_291 = lean_box(0);
x_292 = x_309;
x_293 = x_310;
x_294 = x_311;
x_295 = x_312;
x_296 = x_313;
x_297 = x_314;
x_298 = x_319;
x_299 = x_315;
x_300 = x_316;
x_301 = x_317;
x_302 = x_318;
goto block_307;
}
else
{
if (x_39 == 0)
{
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_310);
lean_dec_ref(x_201);
lean_dec_ref(x_35);
lean_dec(x_29);
lean_dec(x_28);
x_5 = lean_box(0);
x_6 = x_318;
goto block_9;
}
else
{
x_291 = lean_box(0);
x_292 = x_309;
x_293 = x_310;
x_294 = x_311;
x_295 = x_312;
x_296 = x_313;
x_297 = x_314;
x_298 = x_319;
x_299 = x_315;
x_300 = x_316;
x_301 = x_317;
x_302 = x_318;
goto block_307;
}
}
}
block_346:
{
if (x_328 == 0)
{
if (x_330 == 0)
{
x_308 = lean_box(0);
x_309 = x_321;
x_310 = x_322;
x_311 = x_323;
x_312 = x_324;
x_313 = x_331;
x_314 = x_325;
x_315 = x_326;
x_316 = x_327;
x_317 = x_328;
x_318 = x_332;
x_319 = x_330;
goto block_320;
}
else
{
x_308 = lean_box(0);
x_309 = x_321;
x_310 = x_322;
x_311 = x_323;
x_312 = x_324;
x_313 = x_331;
x_314 = x_325;
x_315 = x_326;
x_316 = x_327;
x_317 = x_328;
x_318 = x_332;
x_319 = x_329;
goto block_320;
}
}
else
{
if (x_202 == 0)
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_332);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_332, 2);
lean_inc_ref(x_201);
x_336 = lean_array_push(x_335, x_201);
lean_ctor_set(x_332, 2, x_336);
x_308 = lean_box(0);
x_309 = x_321;
x_310 = x_322;
x_311 = x_323;
x_312 = x_324;
x_313 = x_331;
x_314 = x_325;
x_315 = x_326;
x_316 = x_327;
x_317 = x_328;
x_318 = x_332;
x_319 = x_328;
goto block_320;
}
else
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_337 = lean_ctor_get(x_332, 0);
x_338 = lean_ctor_get(x_332, 1);
x_339 = lean_ctor_get_uint8(x_332, sizeof(void*)*6);
x_340 = lean_ctor_get(x_332, 2);
x_341 = lean_ctor_get(x_332, 3);
x_342 = lean_ctor_get(x_332, 4);
x_343 = lean_ctor_get(x_332, 5);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_332);
lean_inc_ref(x_201);
x_344 = lean_array_push(x_340, x_201);
x_345 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_345, 0, x_337);
lean_ctor_set(x_345, 1, x_338);
lean_ctor_set(x_345, 2, x_344);
lean_ctor_set(x_345, 3, x_341);
lean_ctor_set(x_345, 4, x_342);
lean_ctor_set(x_345, 5, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*6, x_339);
x_308 = lean_box(0);
x_309 = x_321;
x_310 = x_322;
x_311 = x_323;
x_312 = x_324;
x_313 = x_331;
x_314 = x_325;
x_315 = x_326;
x_316 = x_327;
x_317 = x_328;
x_318 = x_345;
x_319 = x_328;
goto block_320;
}
}
else
{
x_308 = lean_box(0);
x_309 = x_321;
x_310 = x_322;
x_311 = x_323;
x_312 = x_324;
x_313 = x_331;
x_314 = x_325;
x_315 = x_326;
x_316 = x_327;
x_317 = x_328;
x_318 = x_332;
x_319 = x_328;
goto block_320;
}
}
}
block_366:
{
if (x_353 == 0)
{
x_321 = x_347;
x_322 = x_348;
x_323 = x_357;
x_324 = x_349;
x_325 = x_350;
x_326 = x_351;
x_327 = x_352;
x_328 = x_354;
x_329 = x_355;
x_330 = x_356;
x_331 = x_2;
x_332 = x_3;
x_333 = lean_box(0);
goto block_346;
}
else
{
if (x_30 == 0)
{
uint8_t x_358; 
lean_inc(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc_ref(x_31);
x_358 = !lean_is_exclusive(x_3);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_3, 5);
lean_dec(x_359);
x_360 = lean_ctor_get(x_3, 4);
lean_dec(x_360);
x_361 = lean_ctor_get(x_3, 3);
lean_dec(x_361);
x_362 = lean_ctor_get(x_3, 2);
lean_dec(x_362);
x_363 = lean_ctor_get(x_3, 1);
lean_dec(x_363);
x_364 = lean_ctor_get(x_3, 0);
lean_dec(x_364);
lean_inc(x_29);
lean_inc(x_28);
lean_ctor_set_uint8(x_3, sizeof(void*)*6, x_353);
x_321 = x_347;
x_322 = x_348;
x_323 = x_357;
x_324 = x_349;
x_325 = x_350;
x_326 = x_351;
x_327 = x_352;
x_328 = x_354;
x_329 = x_355;
x_330 = x_356;
x_331 = x_2;
x_332 = x_3;
x_333 = lean_box(0);
goto block_346;
}
else
{
lean_object* x_365; 
lean_dec(x_3);
lean_inc(x_29);
lean_inc(x_28);
x_365 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_365, 0, x_28);
lean_ctor_set(x_365, 1, x_29);
lean_ctor_set(x_365, 2, x_31);
lean_ctor_set(x_365, 3, x_32);
lean_ctor_set(x_365, 4, x_33);
lean_ctor_set(x_365, 5, x_34);
lean_ctor_set_uint8(x_365, sizeof(void*)*6, x_353);
x_321 = x_347;
x_322 = x_348;
x_323 = x_357;
x_324 = x_349;
x_325 = x_350;
x_326 = x_351;
x_327 = x_352;
x_328 = x_354;
x_329 = x_355;
x_330 = x_356;
x_331 = x_2;
x_332 = x_365;
x_333 = lean_box(0);
goto block_346;
}
}
else
{
x_321 = x_347;
x_322 = x_348;
x_323 = x_357;
x_324 = x_349;
x_325 = x_350;
x_326 = x_351;
x_327 = x_352;
x_328 = x_354;
x_329 = x_355;
x_330 = x_356;
x_331 = x_2;
x_332 = x_3;
x_333 = lean_box(0);
goto block_346;
}
}
}
block_380:
{
uint8_t x_377; 
x_377 = l_Lake_instOrdJobAction_ord(x_38, x_368);
if (x_377 == 2)
{
uint8_t x_378; 
x_378 = 0;
x_347 = x_368;
x_348 = x_367;
x_349 = x_369;
x_350 = x_370;
x_351 = x_372;
x_352 = x_371;
x_353 = x_374;
x_354 = x_373;
x_355 = x_376;
x_356 = x_375;
x_357 = x_378;
goto block_366;
}
else
{
uint8_t x_379; 
x_379 = 1;
x_347 = x_368;
x_348 = x_367;
x_349 = x_369;
x_350 = x_370;
x_351 = x_372;
x_352 = x_371;
x_353 = x_374;
x_354 = x_373;
x_355 = x_376;
x_356 = x_375;
x_357 = x_379;
goto block_366;
}
}
block_394:
{
uint8_t x_390; uint8_t x_391; 
x_390 = lean_strict_and(x_388, x_389);
x_391 = l_Lake_instOrdLogLevel_ord(x_36, x_384);
if (x_391 == 2)
{
uint8_t x_392; 
x_392 = 0;
x_367 = x_382;
x_368 = x_381;
x_369 = x_383;
x_370 = x_384;
x_371 = x_386;
x_372 = x_385;
x_373 = x_390;
x_374 = x_387;
x_375 = x_388;
x_376 = x_392;
goto block_380;
}
else
{
uint8_t x_393; 
x_393 = 1;
x_367 = x_382;
x_368 = x_381;
x_369 = x_383;
x_370 = x_384;
x_371 = x_386;
x_372 = x_385;
x_373 = x_390;
x_374 = x_387;
x_375 = x_388;
x_376 = x_393;
goto block_380;
}
}
block_406:
{
uint8_t x_403; 
x_403 = l_Lake_instOrdLogLevel_ord(x_37, x_398);
if (x_403 == 2)
{
uint8_t x_404; 
x_404 = 0;
x_381 = x_396;
x_382 = x_395;
x_383 = x_397;
x_384 = x_398;
x_385 = x_400;
x_386 = x_399;
x_387 = x_401;
x_388 = x_402;
x_389 = x_404;
goto block_394;
}
else
{
uint8_t x_405; 
x_405 = 1;
x_381 = x_396;
x_382 = x_395;
x_383 = x_397;
x_384 = x_398;
x_385 = x_400;
x_386 = x_399;
x_387 = x_401;
x_388 = x_402;
x_389 = x_405;
goto block_394;
}
}
block_418:
{
lean_object* x_408; uint8_t x_409; uint8_t x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc_ref(x_408);
x_409 = lean_ctor_get_uint8(x_407, sizeof(void*)*3);
x_410 = lean_ctor_get_uint8(x_407, sizeof(void*)*3 + 1);
x_411 = lean_ctor_get(x_407, 2);
lean_inc(x_411);
lean_dec_ref(x_407);
x_412 = l_Lake_Log_maxLv(x_408);
x_413 = lean_array_get_size(x_408);
x_414 = lean_unsigned_to_nat(0u);
x_415 = lean_nat_dec_eq(x_413, x_414);
if (x_415 == 0)
{
uint8_t x_416; 
x_416 = 1;
x_395 = x_408;
x_396 = x_409;
x_397 = x_411;
x_398 = x_412;
x_399 = x_414;
x_400 = x_413;
x_401 = x_410;
x_402 = x_416;
goto block_406;
}
else
{
uint8_t x_417; 
x_417 = 0;
x_395 = x_408;
x_396 = x_409;
x_397 = x_411;
x_398 = x_412;
x_399 = x_414;
x_400 = x_413;
x_401 = x_410;
x_402 = x_417;
goto block_406;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_array_uget(x_1, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_io_get_task_state(x_19);
lean_dec_ref(x_19);
switch (x_20) {
case 0:
{
uint8_t x_21; 
lean_inc(x_17);
lean_inc(x_16);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_push(x_17, x_18);
lean_ctor_set(x_4, 1, x_24);
x_8 = x_4;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_25 = lean_array_push(x_17, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_8 = x_26;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
case 1:
{
uint8_t x_27; 
lean_inc(x_17);
lean_inc(x_16);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_4, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_dec(x_29);
lean_inc(x_18);
x_30 = lean_array_push(x_16, x_18);
x_31 = lean_array_push(x_17, x_18);
lean_ctor_set(x_4, 1, x_31);
lean_ctor_set(x_4, 0, x_30);
x_8 = x_4;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_inc(x_18);
x_32 = lean_array_push(x_16, x_18);
x_33 = lean_array_push(x_17, x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_8 = x_34;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
default: 
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc_ref(x_5);
x_35 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(x_18, x_5, x_6);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_40);
x_8 = x_4;
x_9 = x_36;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
x_43 = lean_ctor_get_uint8(x_36, sizeof(void*)*6);
x_44 = lean_ctor_get(x_36, 2);
x_45 = lean_ctor_get(x_36, 3);
x_46 = lean_ctor_get(x_36, 4);
x_47 = lean_ctor_get(x_36, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_41, x_48);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*6, x_43);
x_8 = x_4;
x_9 = x_50;
x_10 = lean_box(0);
goto block_14;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec_ref(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_mkBuildContext___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_st_ref_take(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lake_mkBuildContext___closed__0;
x_9 = lean_st_ref_set(x_5, x_8);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_array_get_size(x_6);
x_30 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_30);
x_31 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_32 = lean_array_get_size(x_1);
x_33 = lean_nat_dec_lt(x_7, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc_ref(x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_3);
x_13 = x_34;
x_14 = x_31;
x_15 = x_3;
x_16 = lean_box(0);
goto block_25;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_32, x_32);
if (x_35 == 0)
{
if (x_33 == 0)
{
lean_object* x_36; 
lean_inc_ref(x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_3);
x_13 = x_36;
x_14 = x_31;
x_15 = x_3;
x_16 = lean_box(0);
goto block_25;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_32);
lean_inc_ref(x_2);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_37, x_38, x_31, x_2, x_3);
x_26 = x_39;
goto block_29;
}
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_32);
lean_inc_ref(x_2);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_40, x_41, x_31, x_2, x_3);
x_26 = x_42;
goto block_29;
}
}
block_25:
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_7, x_12);
if (x_17 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_13;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_12, x_12);
if (x_18 == 0)
{
if (x_17 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_13;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec_ref(x_13);
x_19 = 0;
x_20 = lean_usize_of_nat(x_12);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_19, x_20, x_14, x_2, x_15);
lean_dec(x_6);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec_ref(x_13);
x_22 = 0;
x_23 = lean_usize_of_nat(x_12);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_22, x_23, x_14, x_2, x_15);
lean_dec(x_6);
return x_24;
}
}
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_13 = x_26;
x_14 = x_27;
x_15 = x_28;
x_16 = lean_box(0);
goto block_25;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_64; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
x_48 = lean_ctor_get(x_3, 4);
x_49 = lean_ctor_get(x_3, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_50 = lean_array_get_size(x_6);
x_68 = lean_nat_add(x_44, x_50);
lean_dec(x_44);
x_69 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_69, 0, x_43);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_46);
lean_ctor_set(x_69, 3, x_47);
lean_ctor_set(x_69, 4, x_48);
lean_ctor_set(x_69, 5, x_49);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_45);
x_70 = l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0;
x_71 = lean_array_get_size(x_1);
x_72 = lean_nat_dec_lt(x_7, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_inc_ref(x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_69);
x_51 = x_73;
x_52 = x_70;
x_53 = x_69;
x_54 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
if (x_72 == 0)
{
lean_object* x_75; 
lean_inc_ref(x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_69);
x_51 = x_75;
x_52 = x_70;
x_53 = x_69;
x_54 = lean_box(0);
goto block_63;
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_71);
lean_inc_ref(x_2);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_76, x_77, x_70, x_2, x_69);
x_64 = x_78;
goto block_67;
}
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_71);
lean_inc_ref(x_2);
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_79, x_80, x_70, x_2, x_69);
x_64 = x_81;
goto block_67;
}
}
block_63:
{
uint8_t x_55; 
x_55 = lean_nat_dec_lt(x_7, x_50);
if (x_55 == 0)
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_51;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_50, x_50);
if (x_56 == 0)
{
if (x_55 == 0)
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_51;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
lean_dec_ref(x_51);
x_57 = 0;
x_58 = lean_usize_of_nat(x_50);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_57, x_58, x_52, x_2, x_53);
lean_dec(x_6);
return x_59;
}
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
lean_dec_ref(x_51);
x_60 = 0;
x_61 = lean_usize_of_nat(x_50);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_60, x_61, x_52, x_2, x_53);
lean_dec(x_6);
return x_62;
}
}
}
block_67:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
x_51 = x_64;
x_52 = x_65;
x_53 = x_66;
x_54 = lean_box(0);
goto block_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_io_mono_ms_now();
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
x_4 = x_2;
x_5 = lean_box(0);
goto block_20;
}
else
{
uint32_t x_28; lean_object* x_29; 
x_28 = lean_uint32_of_nat(x_25);
lean_dec(x_25);
x_29 = l_IO_sleep(x_28);
x_4 = x_2;
x_5 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_mono_ms_now();
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 4);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 4, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_6);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*6, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_2);
x_14 = lean_box(0);
lean_ctor_set(x_6, 1, x_7);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
lean_inc_ref(x_2);
x_15 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_9, x_10, x_2, x_7);
lean_dec(x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_1 = x_10;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_2);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_2);
x_27 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_20, x_21, x_2, x_7);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_1 = x_21;
x_3 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_loop(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_loop(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
lean_ctor_set(x_6, 3, x_10);
x_15 = lean_string_utf8_byte_size(x_9);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 4);
lean_inc_ref(x_20);
lean_dec_ref(x_18);
lean_inc_ref(x_9);
x_26 = lean_apply_2(x_20, x_9, lean_box(0));
if (lean_obj_tag(x_26) == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_9);
x_21 = lean_box(0);
goto block_25;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_30 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_31 = lean_unsigned_to_nat(89u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_34 = lean_io_error_to_string(x_28);
x_35 = lean_string_append(x_33, x_34);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_37 = lean_string_append(x_35, x_36);
x_38 = l_String_quote(x_9);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 0, x_38);
x_39 = l_Std_Format_defWidth;
x_40 = l_Std_Format_pretty(x_26, x_39, x_16, x_16);
x_41 = lean_string_append(x_37, x_40);
lean_dec_ref(x_40);
x_42 = l_mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_41);
lean_dec_ref(x_41);
x_43 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_42);
x_21 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_ctor_get(x_26, 0);
lean_inc(x_44);
lean_dec(x_26);
x_45 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_46 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_47 = lean_unsigned_to_nat(89u);
x_48 = lean_unsigned_to_nat(4u);
x_49 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_50 = lean_io_error_to_string(x_44);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_53 = lean_string_append(x_51, x_52);
x_54 = l_String_quote(x_9);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Std_Format_defWidth;
x_57 = l_Std_Format_pretty(x_55, x_56, x_16, x_16);
x_58 = lean_string_append(x_53, x_57);
lean_dec_ref(x_57);
x_59 = l_mkPanicMessageWithDecl(x_45, x_46, x_47, x_48, x_58);
lean_dec_ref(x_58);
x_60 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_59);
x_21 = lean_box(0);
goto block_25;
}
}
block_25:
{
lean_object* x_22; 
x_22 = lean_apply_1(x_19, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_11 = x_23;
x_12 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_22);
x_24 = lean_box(0);
x_11 = x_24;
x_12 = lean_box(0);
goto block_14;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_6);
return x_62;
}
block_14:
{
lean_object* x_13; 
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_63 = lean_ctor_get(x_6, 0);
x_64 = lean_ctor_get(x_6, 1);
x_65 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_66 = lean_ctor_get(x_6, 2);
x_67 = lean_ctor_get(x_6, 3);
x_68 = lean_ctor_get(x_6, 4);
x_69 = lean_ctor_get(x_6, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_6);
x_70 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_71 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*6, x_65);
x_76 = lean_string_utf8_byte_size(x_67);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_87; 
x_79 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_2);
x_80 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_79, 4);
lean_inc_ref(x_81);
lean_dec_ref(x_79);
lean_inc_ref(x_67);
x_87 = lean_apply_2(x_81, x_67, lean_box(0));
if (lean_obj_tag(x_87) == 0)
{
lean_dec_ref(x_87);
lean_dec_ref(x_67);
x_82 = lean_box(0);
goto block_86;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_91 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_92 = lean_unsigned_to_nat(89u);
x_93 = lean_unsigned_to_nat(4u);
x_94 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_95 = lean_io_error_to_string(x_88);
x_96 = lean_string_append(x_94, x_95);
lean_dec_ref(x_95);
x_97 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_98 = lean_string_append(x_96, x_97);
x_99 = l_String_quote(x_67);
if (lean_is_scalar(x_89)) {
 x_100 = lean_alloc_ctor(3, 1, 0);
} else {
 x_100 = x_89;
 lean_ctor_set_tag(x_100, 3);
}
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Std_Format_defWidth;
x_102 = l_Std_Format_pretty(x_100, x_101, x_77, x_77);
x_103 = lean_string_append(x_98, x_102);
lean_dec_ref(x_102);
x_104 = l_mkPanicMessageWithDecl(x_90, x_91, x_92, x_93, x_103);
lean_dec_ref(x_103);
x_105 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_104);
x_82 = lean_box(0);
goto block_86;
}
block_86:
{
lean_object* x_83; 
x_83 = lean_apply_1(x_80, lean_box(0));
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_72 = x_84;
x_73 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_85; 
lean_dec_ref(x_83);
x_85 = lean_box(0);
x_72 = x_85;
x_73 = lean_box(0);
goto block_75;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_67);
lean_dec(x_7);
lean_dec_ref(x_2);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_71);
return x_107;
}
block_75:
{
lean_object* x_74; 
if (lean_is_scalar(x_7)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_7;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_main(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Array_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Lake_OutStream_get(x_9);
lean_inc_ref(x_10);
x_11 = l_Lake_AnsiMode_isEnabled(x_10, x_8);
x_12 = l_Lake_BuildConfig_showProgress(x_1);
x_13 = 2;
x_14 = l_Lake_instDecidableEqVerbosity(x_5, x_13);
if (x_14 == 0)
{
uint8_t x_23; 
x_23 = 2;
x_20 = x_23;
goto block_22;
}
else
{
uint8_t x_24; 
x_24 = 0;
x_20 = x_24;
goto block_22;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(100u);
x_18 = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 2, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 3, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 4, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 5, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 6, x_16);
return x_18;
}
block_22:
{
if (x_14 == 0)
{
if (x_11 == 0)
{
uint8_t x_21; 
x_21 = 1;
x_15 = x_20;
x_16 = x_21;
goto block_19;
}
else
{
x_15 = x_20;
x_16 = x_14;
goto block_19;
}
}
else
{
x_15 = x_20;
x_16 = x_14;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_io_mono_ms_now();
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set(x_9, 5, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*6, x_8);
x_10 = l___private_Lake_Build_Run_0__Lake_Monitor_main(x_2, x_1, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 3, 7);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 4, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 5, x_9);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 6, x_10);
x_16 = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(x_15, x_1, x_12, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = lean_unbox(x_8);
x_20 = lean_unbox(x_9);
x_21 = lean_unbox(x_10);
x_22 = l_Lake_monitorJobs(x_1, x_2, x_3, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_11, x_12, x_13);
return x_22;
}
}
static uint32_t _init_l_Lake_noBuildCode() {
_start:
{
uint32_t x_1; 
x_1 = 3;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_45; uint8_t x_121; 
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
x_121 = l_Lake_Workspace_isRootArtifactCacheWritable(x_2);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_2, 0);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = l_Lean_Name_toString(x_123, x_121);
x_125 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
x_126 = lean_string_append(x_124, x_125);
x_127 = 2;
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = lean_apply_2(x_1, x_128, lean_box(0));
x_45 = lean_box(0);
goto block_120;
}
else
{
lean_dec_ref(x_1);
x_45 = lean_box(0);
goto block_120;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
block_27:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_12);
x_16 = lean_box(0);
x_17 = lean_nat_dec_lt(x_13, x_15);
if (x_17 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_10);
return x_16;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
if (x_17 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_10);
return x_16;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_15);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_11, x_10, x_12, x_19, x_20, x_16);
x_22 = lean_apply_1(x_21, lean_box(0));
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_15);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_11, x_10, x_12, x_23, x_24, x_16);
x_26 = lean_apply_1(x_25, lean_box(0));
return x_26;
}
}
}
block_44:
{
if (x_5 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_29);
lean_dec_ref(x_10);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_array_get_size(x_29);
x_33 = lean_box(0);
x_34 = lean_nat_dec_lt(x_28, x_32);
if (x_34 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_10);
return x_33;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_32, x_32);
if (x_35 == 0)
{
if (x_34 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_10);
return x_33;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_32);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_11, x_10, x_29, x_36, x_37, x_33);
x_39 = lean_apply_1(x_38, lean_box(0));
return x_39;
}
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_32);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_11, x_10, x_29, x_40, x_41, x_33);
x_43 = lean_apply_1(x_42, lean_box(0));
return x_43;
}
}
}
}
block_120:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_46);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_46, 23);
lean_inc(x_47);
lean_dec_ref(x_46);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_st_ref_get(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0;
x_52 = l_Lake_CacheMap_writeFile(x_4, x_49, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_eq(x_54, x_50);
if (x_55 == 0)
{
if (x_5 == 0)
{
lean_dec(x_53);
lean_dec_ref(x_10);
lean_dec_ref(x_3);
x_7 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_56);
lean_dec_ref(x_3);
x_57 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
x_58 = lean_apply_2(x_56, x_57, lean_box(0));
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_12 = x_53;
x_13 = x_50;
x_14 = lean_box(0);
goto block_27;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_61 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_62 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_63 = lean_unsigned_to_nat(89u);
x_64 = lean_unsigned_to_nat(4u);
x_65 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_66 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_67 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_66, x_5);
x_68 = lean_string_append(x_65, x_67);
lean_dec_ref(x_67);
x_69 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_io_error_to_string(x_59);
x_72 = lean_string_append(x_70, x_71);
lean_dec_ref(x_71);
x_73 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_74 = lean_string_append(x_72, x_73);
x_75 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4;
x_76 = lean_string_append(x_74, x_75);
x_77 = l_mkPanicMessageWithDecl(x_61, x_62, x_63, x_64, x_76);
lean_dec_ref(x_76);
x_78 = l_panic___redArg(x_60, x_77);
x_79 = lean_apply_1(x_78, lean_box(0));
x_12 = x_53;
x_13 = x_50;
x_14 = lean_box(0);
goto block_27;
}
}
}
else
{
lean_dec(x_53);
lean_dec_ref(x_10);
lean_dec_ref(x_3);
x_7 = lean_box(0);
goto block_9;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_52, 1);
lean_inc(x_80);
lean_dec_ref(x_52);
x_81 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_81);
lean_dec_ref(x_3);
x_82 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
x_83 = lean_apply_2(x_81, x_82, lean_box(0));
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
x_28 = x_50;
x_29 = x_80;
x_30 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_86 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_87 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_88 = lean_unsigned_to_nat(89u);
x_89 = lean_unsigned_to_nat(4u);
x_90 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_91 = lean_io_error_to_string(x_84);
x_92 = lean_string_append(x_90, x_91);
lean_dec_ref(x_91);
x_93 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_94 = lean_string_append(x_92, x_93);
x_95 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_mkPanicMessageWithDecl(x_86, x_87, x_88, x_89, x_96);
lean_dec_ref(x_96);
x_98 = l_panic___redArg(x_85, x_97);
x_99 = lean_apply_1(x_98, lean_box(0));
x_28 = x_50;
x_29 = x_80;
x_30 = lean_box(0);
goto block_44;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_47);
lean_dec_ref(x_10);
lean_dec_ref(x_4);
x_100 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_100);
lean_dec_ref(x_3);
x_101 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
x_102 = lean_apply_2(x_100, x_101, lean_box(0));
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
x_106 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_107 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_108 = lean_unsigned_to_nat(89u);
x_109 = lean_unsigned_to_nat(4u);
x_110 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_111 = lean_io_error_to_string(x_104);
x_112 = lean_string_append(x_110, x_111);
lean_dec_ref(x_111);
x_113 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_114 = lean_string_append(x_112, x_113);
x_115 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12;
x_116 = lean_string_append(x_114, x_115);
x_117 = l_mkPanicMessageWithDecl(x_106, x_107, x_108, x_109, x_116);
lean_dec_ref(x_116);
x_118 = l_panic___redArg(x_105, x_117);
x_119 = lean_apply_1(x_118, lean_box(0));
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_array_uget(x_2, x_3);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
x_19 = lean_string_append(x_17, x_18);
lean_inc_ref(x_14);
lean_inc_ref(x_19);
x_20 = lean_apply_2(x_14, x_19, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_7 = x_21;
x_8 = lean_box(0);
goto block_12;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_25 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_26 = lean_unsigned_to_nat(89u);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_30 = lean_io_error_to_string(x_23);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_33 = lean_string_append(x_31, x_32);
x_34 = l_String_quote(x_19);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 0, x_34);
x_35 = l_Std_Format_defWidth;
x_36 = l_Std_Format_pretty(x_20, x_35, x_28, x_28);
x_37 = lean_string_append(x_33, x_36);
lean_dec_ref(x_36);
x_38 = l_mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_37);
lean_dec_ref(x_37);
x_39 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_38);
x_7 = x_39;
x_8 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_42 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_43 = lean_unsigned_to_nat(89u);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_47 = lean_io_error_to_string(x_40);
x_48 = lean_string_append(x_46, x_47);
lean_dec_ref(x_47);
x_49 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_50 = lean_string_append(x_48, x_49);
x_51 = l_String_quote(x_19);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Std_Format_defWidth;
x_54 = l_Std_Format_pretty(x_52, x_53, x_45, x_45);
x_55 = lean_string_append(x_50, x_54);
lean_dec_ref(x_54);
x_56 = l_mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_55);
lean_dec_ref(x_55);
x_57 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_56);
x_7 = x_57;
x_8 = lean_box(0);
goto block_12;
}
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Run_0__Lake_reportResult___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = l___private_Lake_Build_Run_0__Lake_reportResult___closed__7;
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_126; 
x_115 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
lean_dec_ref(x_3);
x_126 = l_Array_isEmpty___redArg(x_115);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_134; lean_object* x_136; lean_object* x_149; lean_object* x_150; 
lean_dec(x_116);
x_127 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_2, 4);
x_149 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
lean_inc_ref(x_128);
x_150 = lean_apply_2(x_128, x_149, lean_box(0));
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
x_136 = lean_box(0);
goto block_148;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_153 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_154 = lean_unsigned_to_nat(89u);
x_155 = lean_unsigned_to_nat(4u);
x_156 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_157 = lean_io_error_to_string(x_151);
x_158 = lean_string_append(x_156, x_157);
lean_dec_ref(x_157);
x_159 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_160 = lean_string_append(x_158, x_159);
x_161 = l___private_Lake_Build_Run_0__Lake_reportResult___closed__8;
x_162 = lean_string_append(x_160, x_161);
x_163 = l_mkPanicMessageWithDecl(x_152, x_153, x_154, x_155, x_162);
lean_dec_ref(x_162);
x_164 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_163);
x_136 = lean_box(0);
goto block_148;
}
block_133:
{
lean_object* x_130; 
x_130 = lean_apply_1(x_127, lean_box(0));
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec_ref(x_130);
x_132 = lean_box(0);
return x_132;
}
}
block_135:
{
x_129 = lean_box(0);
goto block_133;
}
block_148:
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_array_get_size(x_115);
x_139 = lean_nat_dec_lt(x_137, x_138);
if (x_139 == 0)
{
lean_dec_ref(x_115);
lean_dec_ref(x_2);
x_129 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_box(0);
x_141 = lean_nat_dec_le(x_138, x_138);
if (x_141 == 0)
{
if (x_139 == 0)
{
lean_dec_ref(x_115);
lean_dec_ref(x_2);
x_129 = lean_box(0);
goto block_133;
}
else
{
size_t x_142; size_t x_143; lean_object* x_144; 
x_142 = 0;
x_143 = lean_usize_of_nat(x_138);
x_144 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(x_2, x_115, x_142, x_143, x_140);
lean_dec_ref(x_115);
x_134 = x_144;
goto block_135;
}
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = 0;
x_146 = lean_usize_of_nat(x_138);
x_147 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(x_2, x_115, x_145, x_146, x_140);
lean_dec_ref(x_115);
x_134 = x_147;
goto block_135;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec_ref(x_115);
x_165 = l_Lake_BuildConfig_showProgress(x_1);
if (x_165 == 0)
{
x_117 = x_165;
goto block_125;
}
else
{
uint8_t x_166; 
x_166 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_117 = x_166;
goto block_125;
}
}
block_114:
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0));
x_10 = lean_string_append(x_9, x_6);
lean_dec_ref(x_6);
x_11 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
x_12 = lean_string_append(x_10, x_11);
lean_inc_ref(x_12);
x_13 = lean_apply_2(x_8, x_12, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_18 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_19 = lean_unsigned_to_nat(89u);
x_20 = lean_unsigned_to_nat(4u);
x_21 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_22 = lean_unsigned_to_nat(0u);
x_23 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_24 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_23, x_5);
x_25 = lean_string_append(x_21, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_io_error_to_string(x_16);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_31 = lean_string_append(x_29, x_30);
x_32 = l_String_quote(x_12);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_32);
x_33 = l_Std_Format_defWidth;
x_34 = l_Std_Format_pretty(x_13, x_33, x_22, x_22);
x_35 = lean_string_append(x_31, x_34);
lean_dec_ref(x_34);
x_36 = l_mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_35);
lean_dec_ref(x_35);
x_37 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_40 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_41 = lean_unsigned_to_nat(89u);
x_42 = lean_unsigned_to_nat(4u);
x_43 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_44 = lean_unsigned_to_nat(0u);
x_45 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_46 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_45, x_5);
x_47 = lean_string_append(x_43, x_46);
lean_dec_ref(x_46);
x_48 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_io_error_to_string(x_38);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_53 = lean_string_append(x_51, x_52);
x_54 = l_String_quote(x_12);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Std_Format_defWidth;
x_57 = l_Std_Format_pretty(x_55, x_56, x_44, x_44);
x_58 = lean_string_append(x_53, x_57);
lean_dec_ref(x_57);
x_59 = l_mkPanicMessageWithDecl(x_39, x_40, x_41, x_42, x_58);
lean_dec_ref(x_58);
x_60 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_61);
lean_dec_ref(x_2);
x_62 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
x_63 = lean_string_append(x_62, x_6);
lean_dec_ref(x_6);
x_64 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
x_65 = lean_string_append(x_63, x_64);
lean_inc_ref(x_65);
x_66 = lean_apply_2(x_61, x_65, lean_box(0));
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_71 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_72 = lean_unsigned_to_nat(89u);
x_73 = lean_unsigned_to_nat(4u);
x_74 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_75 = lean_unsigned_to_nat(0u);
x_76 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_77 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_76, x_7);
x_78 = lean_string_append(x_74, x_77);
lean_dec_ref(x_77);
x_79 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_io_error_to_string(x_69);
x_82 = lean_string_append(x_80, x_81);
lean_dec_ref(x_81);
x_83 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_84 = lean_string_append(x_82, x_83);
x_85 = l_String_quote(x_65);
lean_ctor_set_tag(x_66, 3);
lean_ctor_set(x_66, 0, x_85);
x_86 = l_Std_Format_defWidth;
x_87 = l_Std_Format_pretty(x_66, x_86, x_75, x_75);
x_88 = lean_string_append(x_84, x_87);
lean_dec_ref(x_87);
x_89 = l_mkPanicMessageWithDecl(x_70, x_71, x_72, x_73, x_88);
lean_dec_ref(x_88);
x_90 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_91 = lean_ctor_get(x_66, 0);
lean_inc(x_91);
lean_dec(x_66);
x_92 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_93 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_94 = lean_unsigned_to_nat(89u);
x_95 = lean_unsigned_to_nat(4u);
x_96 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_97 = lean_unsigned_to_nat(0u);
x_98 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_99 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_98, x_7);
x_100 = lean_string_append(x_96, x_99);
lean_dec_ref(x_99);
x_101 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_io_error_to_string(x_91);
x_104 = lean_string_append(x_102, x_103);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_106 = lean_string_append(x_104, x_105);
x_107 = l_String_quote(x_65);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Std_Format_defWidth;
x_110 = l_Std_Format_pretty(x_108, x_109, x_97, x_97);
x_111 = lean_string_append(x_106, x_110);
lean_dec_ref(x_110);
x_112 = l_mkPanicMessageWithDecl(x_92, x_93, x_94, x_95, x_111);
lean_dec_ref(x_111);
x_113 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_112);
return x_113;
}
}
}
}
block_125:
{
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_116);
lean_dec_ref(x_2);
x_118 = lean_box(0);
return x_118;
}
else
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_dec_eq(x_116, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = l_Nat_reprFast(x_116);
x_122 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
x_123 = lean_string_append(x_121, x_122);
x_5 = x_117;
x_6 = x_123;
goto block_114;
}
else
{
lean_object* x_124; 
lean_dec(x_116);
x_124 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
x_5 = x_117;
x_6 = x_124;
goto block_114;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_reportResult(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0));
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_2);
x_4 = l_Lake_Job_toOpaque___redArg(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0;
x_6 = lean_array_push(x_5, x_4);
x_7 = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1;
x_8 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_9 = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(x_1, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = l_Array_isEmpty___redArg(x_10);
lean_dec_ref(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_12 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3));
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
x_15 = lean_io_wait(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__5));
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_27 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__5));
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_monitorJob(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_Env_leanGithash(x_4);
x_6 = l_Lake_Hash_nil;
x_7 = lean_string_hash(x_5);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lake_mkBuildContext___closed__4;
x_10 = lean_string_append(x_9, x_5);
lean_dec_ref(x_5);
x_11 = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0;
x_12 = l_Lake_mkBuildContext___closed__6;
x_13 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set_uint64(x_13, sizeof(void*)*3, x_8);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_10, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_7, 0, x_13);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_22);
lean_dec(x_7);
x_27 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_22, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_24);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_24);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_box(1);
x_8 = lean_st_mk_ref(x_7);
x_9 = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_box(0);
x_11 = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(x_1, x_2, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0));
lean_inc(x_8);
x_16 = l_Lake_Job_async___redArg(x_10, x_9, x_12, x_5, x_15, x_14, x_13, x_8, x_11);
x_17 = lean_st_ref_get(x_8);
lean_dec(x_8);
lean_dec(x_17);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_array_uget(x_4, x_5);
lean_inc_ref(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_2, x_3);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_7 = x_11;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_9, x_10, x_4, x_11, x_12, x_7);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_41; uint8_t x_111; 
x_111 = l_Lake_Workspace_isRootArtifactCacheWritable(x_4);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_4, 0);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = l_Lean_Name_toString(x_113, x_111);
x_115 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
x_116 = lean_string_append(x_114, x_115);
x_117 = 2;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
lean_inc_ref(x_1);
x_119 = l_Lake_logToStream(x_118, x_1, x_2, x_3);
lean_dec_ref(x_118);
x_41 = lean_box(0);
goto block_110;
}
else
{
x_41 = lean_box(0);
goto block_110;
}
block_11:
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
block_25:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_13);
x_16 = lean_box(0);
x_17 = lean_nat_dec_lt(x_12, x_15);
if (x_17 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_1);
return x_16;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
if (x_17 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_1);
return x_16;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_15);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_13, x_19, x_20, x_16);
lean_dec_ref(x_13);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_15);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_13, x_22, x_23, x_16);
lean_dec_ref(x_13);
return x_24;
}
}
}
block_40:
{
if (x_7 == 0)
{
lean_object* x_29; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_26);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_27, x_30);
if (x_32 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_1);
return x_31;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
if (x_32 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_1);
return x_31;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_26, x_34, x_35, x_31);
lean_dec_ref(x_26);
return x_36;
}
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_30);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_26, x_37, x_38, x_31);
lean_dec_ref(x_26);
return x_39;
}
}
}
}
block_110:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_42);
lean_dec_ref(x_4);
x_43 = lean_ctor_get(x_42, 23);
lean_inc(x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_st_ref_get(x_44);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0;
x_48 = l_Lake_CacheMap_writeFile(x_6, x_45, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_eq(x_50, x_46);
if (x_51 == 0)
{
if (x_7 == 0)
{
lean_dec(x_49);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_52);
lean_dec_ref(x_5);
x_53 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
x_54 = lean_apply_2(x_52, x_53, lean_box(0));
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_12 = x_46;
x_13 = x_49;
x_14 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_57 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_58 = lean_unsigned_to_nat(89u);
x_59 = lean_unsigned_to_nat(4u);
x_60 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_61 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_62 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_61, x_7);
x_63 = lean_string_append(x_60, x_62);
lean_dec_ref(x_62);
x_64 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_io_error_to_string(x_55);
x_67 = lean_string_append(x_65, x_66);
lean_dec_ref(x_66);
x_68 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_69 = lean_string_append(x_67, x_68);
x_70 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4;
x_71 = lean_string_append(x_69, x_70);
x_72 = l_mkPanicMessageWithDecl(x_56, x_57, x_58, x_59, x_71);
lean_dec_ref(x_71);
x_73 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_72);
x_12 = x_46;
x_13 = x_49;
x_14 = lean_box(0);
goto block_25;
}
}
}
else
{
lean_dec(x_49);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_11;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_48, 1);
lean_inc(x_74);
lean_dec_ref(x_48);
x_75 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_75);
lean_dec_ref(x_5);
x_76 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
x_77 = lean_apply_2(x_75, x_76, lean_box(0));
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_77);
x_26 = x_74;
x_27 = x_46;
x_28 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_80 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_81 = lean_unsigned_to_nat(89u);
x_82 = lean_unsigned_to_nat(4u);
x_83 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_84 = lean_io_error_to_string(x_78);
x_85 = lean_string_append(x_83, x_84);
lean_dec_ref(x_84);
x_86 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_87 = lean_string_append(x_85, x_86);
x_88 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
x_89 = lean_string_append(x_87, x_88);
x_90 = l_mkPanicMessageWithDecl(x_79, x_80, x_81, x_82, x_89);
lean_dec_ref(x_89);
x_91 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_90);
x_26 = x_74;
x_27 = x_46;
x_28 = lean_box(0);
goto block_40;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_43);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_92);
lean_dec_ref(x_5);
x_93 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
x_94 = lean_apply_2(x_92, x_93, lean_box(0));
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_98 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_99 = lean_unsigned_to_nat(89u);
x_100 = lean_unsigned_to_nat(4u);
x_101 = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
x_102 = lean_io_error_to_string(x_96);
x_103 = lean_string_append(x_101, x_102);
lean_dec_ref(x_102);
x_104 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_105 = lean_string_append(x_103, x_104);
x_106 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12;
x_107 = lean_string_append(x_105, x_106);
x_108 = l_mkPanicMessageWithDecl(x_97, x_98, x_99, x_100, x_107);
lean_dec_ref(x_107);
x_109 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_108);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_7);
x_12 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_11);
return x_12;
}
}
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 3;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_4);
lean_inc_ref(x_14);
lean_inc_ref(x_11);
x_16 = l___private_Lake_Build_Run_0__Lake_reportResult(x_2, x_11, x_14);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec_ref(x_2);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec_ref(x_19);
if (x_18 == 2)
{
uint8_t x_34; 
x_34 = 1;
x_31 = x_34;
goto block_33;
}
else
{
uint8_t x_35; 
x_35 = 0;
x_31 = x_35;
goto block_33;
}
block_33:
{
lean_object* x_32; 
lean_inc_ref(x_11);
x_32 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(x_11, x_12, x_13, x_1, x_11, x_30, x_31);
x_20 = lean_box(0);
goto block_29;
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_20 = lean_box(0);
goto block_29;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_mk_io_user_error(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_29:
{
if (lean_obj_tag(x_15) == 0)
{
if (x_17 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec_ref(x_15);
x_6 = lean_box(0);
x_7 = x_21;
goto block_10;
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec_ref(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec_ref(x_15);
x_6 = lean_box(0);
x_7 = x_23;
goto block_10;
}
else
{
uint8_t x_24; lean_object* x_25; 
lean_dec_ref(x_15);
x_24 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0;
x_25 = lean_io_exit(x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_14);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_ctor_set_tag(x_15, 0);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lake_mkBuildContext___closed__0;
x_7 = lean_st_mk_ref(x_6);
lean_inc(x_7);
x_8 = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(x_3, x_7);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_9 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(x_1, x_3, x_7, x_2, x_4);
lean_inc_ref(x_8);
x_10 = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(x_8, x_9);
x_11 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(x_1, x_3, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Workspace_runFetchM(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(x_1, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 1, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = lean_io_wait(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_ctor_set(x_5, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_21);
lean_free_object(x_5);
x_23 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
lean_ctor_set(x_4, 1, x_23);
return x_4;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_26);
lean_dec(x_24);
x_27 = lean_io_wait(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_ctor_set(x_5, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_27);
lean_free_object(x_5);
x_30 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_33);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_34 = x_4;
} else {
 lean_dec_ref(x_4);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_35);
lean_dec(x_32);
x_36 = lean_io_wait(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_36);
x_40 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Run_0__Lake_monitorBuild(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_mkBuildContext___closed__0;
x_5 = lean_st_mk_ref(x_4);
x_6 = 0;
x_7 = 1;
x_8 = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__1));
lean_inc(x_5);
x_9 = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(x_8, x_5);
x_10 = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
x_11 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(x_1, x_8, x_5, x_2, x_10);
x_12 = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(x_9, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec_ref(x_13);
return x_6;
}
else
{
lean_dec_ref(x_13);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_Workspace_checkNoBuild___redArg(x_1, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_checkNoBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = l_Lake_Workspace_checkNoBuild___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_checkNoBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lake_Workspace_checkNoBuild(x_1, x_2, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lake_mkBuildContext___closed__0;
x_6 = lean_st_mk_ref(x_5);
lean_inc(x_6);
x_7 = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(x_3, x_6);
x_8 = ((lean_object*)(l_Lake_Workspace_checkNoBuild___redArg___closed__2));
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_9 = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(x_1, x_3, x_6, x_2, x_8);
lean_inc_ref(x_7);
x_10 = l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(x_7, x_9);
x_11 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg(x_1, x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runBuild___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runBuild___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runBuild(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runBuild___redArg(x_3, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_runBuild___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runBuild___redArg(x_4, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_runBuild(x_1, x_2, x_3, x_4);
return x_6;
}
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
l_Lake_mkBuildContext___closed__0 = _init_l_Lake_mkBuildContext___closed__0();
lean_mark_persistent(l_Lake_mkBuildContext___closed__0);
l_Lake_mkBuildContext___closed__2 = _init_l_Lake_mkBuildContext___closed__2();
lean_mark_persistent(l_Lake_mkBuildContext___closed__2);
l_Lake_mkBuildContext___closed__4 = _init_l_Lake_mkBuildContext___closed__4();
lean_mark_persistent(l_Lake_mkBuildContext___closed__4);
l_Lake_mkBuildContext___closed__5 = _init_l_Lake_mkBuildContext___closed__5();
lean_mark_persistent(l_Lake_mkBuildContext___closed__5);
l_Lake_mkBuildContext___closed__6 = _init_l_Lake_mkBuildContext___closed__6();
lean_mark_persistent(l_Lake_mkBuildContext___closed__6);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__2);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__3);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__4);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__5);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__6);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__7);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8___boxed__const__1);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__8);
l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__17 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__18 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18);
l___private_Lake_Build_Run_0__Lake_print_x21___closed__20 = _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0);
l_Lake_noBuildCode = _init_l_Lake_noBuildCode();
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
l___private_Lake_Build_Run_0__Lake_reportResult___closed__6 = _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
l___private_Lake_Build_Run_0__Lake_reportResult___closed__7 = _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
l___private_Lake_Build_Run_0__Lake_reportResult___closed__8 = _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0);
l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1 = _init_l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1);
l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0();
lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0);
l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0 = _init_l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
