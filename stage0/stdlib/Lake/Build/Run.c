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
static const lean_array_object l_Lake_mkBuildContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_mkBuildContext___closed__0 = (const lean_object*)&l_Lake_mkBuildContext___closed__0_value;
static const lean_string_object l_Lake_mkBuildContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Lean "};
static const lean_object* l_Lake_mkBuildContext___closed__1 = (const lean_object*)&l_Lake_mkBuildContext___closed__1_value;
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_mkBuildContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__2;
static const lean_string_object l_Lake_mkBuildContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l_Lake_mkBuildContext___closed__3 = (const lean_object*)&l_Lake_mkBuildContext___closed__3_value;
static lean_once_cell_t l_Lake_mkBuildContext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__4;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lake_mkBuildContext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__5;
static lean_once_cell_t l_Lake_mkBuildContext___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_mkBuildContext___closed__6;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
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
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0;
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__0;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__17;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " failed: "};
static const lean_object* l___private_Lake_Build_Run_0__Lake_print_x21___closed__19 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static const lean_array_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_value;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "There were issues saving input-to-output mappings from the build:\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Failed to save input-to-output mappings from the build.\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8;
static const lean_string_object l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"};
static const lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_value;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
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
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_io_wait(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0 = (const lean_object*)&l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value;
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
static lean_once_cell_t l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_object* _init_l_Lake_mkBuildContext___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore;
x_2 = ((lean_object*)(l_Lake_mkBuildContext___closed__1));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_mkBuildContext___closed__3));
x_2 = lean_obj_once(&l_Lake_mkBuildContext___closed__2, &l_Lake_mkBuildContext___closed__2_once, _init_l_Lake_mkBuildContext___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkBuildContext___closed__6(void) {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_obj_once(&l_Lake_mkBuildContext___closed__5, &l_Lake_mkBuildContext___closed__5_once, _init_l_Lake_mkBuildContext___closed__5);
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
x_4 = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
x_5 = lean_st_mk_ref(x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lake_Env_leanGithash(x_6);
x_8 = l_Lake_Hash_nil;
x_9 = lean_string_hash(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
x_12 = lean_string_append(x_11, x_7);
lean_dec_ref(x_7);
x_13 = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10493;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10491;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10431;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10367;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10463;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10479;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10487;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10494;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8;
x_4 = lean_array_push(x_2, x_3);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7;
x_6 = lean_array_push(x_4, x_5);
x_7 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6;
x_8 = lean_array_push(x_6, x_7);
x_9 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5;
x_10 = lean_array_push(x_8, x_9);
x_11 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4;
x_12 = lean_array_push(x_10, x_11);
x_13 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3;
x_14 = lean_array_push(x_12, x_13);
x_15 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2;
x_16 = lean_array_push(x_14, x_15);
x_17 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1;
x_18 = lean_array_push(x_16, x_17);
return x_18;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0);
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
x_3 = l_instInhabitedOfMonad___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__17, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17);
x_2 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_2 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__18, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__18);
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_32; 
x_7 = lean_ctor_get(x_5, 0);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
x_8 = x_5;
x_9 = x_32;
goto block_31;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
x_11 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_12 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_13 = lean_unsigned_to_nat(89u);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_17 = lean_io_error_to_string(x_7);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_20 = lean_string_append(x_18, x_19);
x_21 = l_String_quote(x_2);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 0, x_21);
x_22 = x_8;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_21);
x_22 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Std_Format_defWidth;
x_24 = l_Std_Format_pretty(x_22, x_23, x_15, x_15);
x_25 = lean_string_append(x_20, x_24);
lean_dec_ref(x_24);
x_26 = l_mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_25);
lean_dec_ref(x_25);
x_27 = l_panic___redArg(x_10, x_26);
x_28 = lean_apply_1(x_27, lean_box(0));
return x_28;
}
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
lean_object* x_5; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
lean_inc_ref(x_1);
x_10 = lean_apply_2(x_9, x_1, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_5 = x_11;
goto block_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_37; 
x_12 = lean_ctor_get(x_10, 0);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
x_13 = x_10;
x_14 = x_37;
goto block_36;
}
else
{
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
x_16 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_17 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_18 = lean_unsigned_to_nat(89u);
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_22 = lean_io_error_to_string(x_12);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_25 = lean_string_append(x_23, x_24);
x_26 = l_String_quote(x_1);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_26);
x_27 = x_13;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_26);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Std_Format_defWidth;
x_29 = l_Std_Format_pretty(x_27, x_28, x_20, x_20);
x_30 = lean_string_append(x_25, x_29);
lean_dec_ref(x_29);
x_31 = l_mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_30);
lean_dec_ref(x_30);
x_32 = l_panic___redArg(x_15, x_31);
x_33 = lean_apply_1(x_32, lean_box(0));
x_5 = x_33;
goto block_7;
}
}
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
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
lean_object* x_4; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_1(x_8, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_4 = x_10;
goto block_6;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_4 = x_11;
goto block_6;
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
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
x_3 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0(void) {
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_106; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
x_106 = !lean_is_exclusive(x_4);
if (x_106 == 0)
{
x_18 = x_4;
x_19 = x_106;
goto block_105;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_3);
x_21 = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
x_22 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
x_23 = lean_array_fget(x_21, x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Fin_add(x_22, x_17, x_24);
lean_dec(x_17);
x_26 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0));
lean_inc(x_12);
lean_inc(x_11);
if (x_19 == 0)
{
lean_ctor_set(x_18, 5, x_25);
lean_ctor_set(x_18, 3, x_26);
x_27 = x_18;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_104, 0, x_11);
lean_ctor_set(x_104, 1, x_12);
lean_ctor_set(x_104, 2, x_14);
lean_ctor_set(x_104, 3, x_26);
lean_ctor_set(x_104, 4, x_16);
lean_ctor_set(x_104, 5, x_25);
lean_ctor_set_uint8(x_104, sizeof(void*)*6, x_13);
x_27 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_28; lean_object* x_36; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get_size(x_1);
x_85 = lean_nat_dec_lt(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_array_get_size(x_2);
x_87 = lean_nat_sub(x_86, x_24);
x_88 = lean_array_fget_borrowed(x_2, x_87);
lean_dec(x_87);
x_89 = lean_ctor_get(x_88, 2);
x_90 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
x_91 = lean_string_append(x_90, x_89);
x_36 = x_91;
goto block_82;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_92 = lean_nat_sub(x_84, x_24);
x_93 = lean_array_fget_borrowed(x_1, x_92);
x_94 = lean_ctor_get(x_93, 2);
x_95 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4));
x_96 = lean_string_append(x_95, x_94);
x_97 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5));
x_98 = lean_string_append(x_96, x_97);
x_99 = l_Nat_reprFast(x_92);
x_100 = lean_string_append(x_98, x_99);
lean_dec_ref(x_99);
x_101 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6));
x_102 = lean_string_append(x_100, x_101);
x_36 = x_102;
goto block_82;
}
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_20);
x_32 = lean_apply_1(x_31, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_28 = x_33;
goto block_30;
}
else
{
lean_object* x_34; 
lean_dec_ref(x_32);
x_34 = lean_box(0);
x_28 = x_34;
goto block_30;
}
}
block_82:
{
lean_object* x_37; lean_object* x_38; uint32_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_37 = lean_ctor_get(x_20, 4);
x_38 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_39 = lean_unbox_uint32(x_23);
lean_dec(x_23);
x_40 = lean_string_push(x_38, x_39);
x_41 = lean_string_append(x_15, x_40);
lean_dec_ref(x_40);
x_42 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
x_43 = lean_string_append(x_41, x_42);
x_44 = l_Nat_reprFast(x_11);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Nat_reprFast(x_12);
x_49 = lean_string_append(x_47, x_48);
lean_dec_ref(x_48);
x_50 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_36);
lean_dec_ref(x_36);
lean_inc_ref(x_37);
lean_inc_ref(x_52);
x_53 = lean_apply_2(x_37, x_52, lean_box(0));
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
goto block_35;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_81; 
x_54 = lean_ctor_get(x_53, 0);
x_81 = !lean_is_exclusive(x_53);
if (x_81 == 0)
{
x_55 = x_53;
x_56 = x_81;
goto block_80;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_58 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_59 = lean_unsigned_to_nat(89u);
x_60 = lean_unsigned_to_nat(4u);
x_61 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_62 = lean_unsigned_to_nat(0u);
x_63 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_64 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_63, x_10);
x_65 = lean_string_append(x_61, x_64);
lean_dec_ref(x_64);
x_66 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_io_error_to_string(x_54);
x_69 = lean_string_append(x_67, x_68);
lean_dec_ref(x_68);
x_70 = lean_string_append(x_69, x_50);
x_71 = l_String_quote(x_52);
if (x_56 == 0)
{
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_71);
x_72 = x_55;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_71);
x_72 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = l_Std_Format_defWidth;
x_74 = l_Std_Format_pretty(x_72, x_73, x_62, x_62);
x_75 = lean_string_append(x_70, x_74);
lean_dec_ref(x_74);
x_76 = l_mkPanicMessageWithDecl(x_57, x_58, x_59, x_60, x_75);
lean_dec_ref(x_75);
x_77 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_76);
goto block_35;
}
}
}
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
x_11 = lean_array_uget_borrowed(x_4, x_5);
lean_inc_ref(x_1);
x_12 = l_Lake_logToStream(x_11, x_1, x_2, x_3);
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
lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint32_t x_155; lean_object* x_156; uint8_t x_179; uint8_t x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint32_t x_190; uint8_t x_193; uint8_t x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint32_t x_204; lean_object* x_205; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; uint32_t x_224; uint8_t x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; uint8_t x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; uint8_t x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; uint8_t x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; uint8_t x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; lean_object* x_292; uint8_t x_293; uint8_t x_294; uint8_t x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; uint8_t x_314; uint8_t x_315; lean_object* x_316; uint8_t x_317; uint8_t x_318; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; uint8_t x_329; lean_object* x_330; uint8_t x_331; uint8_t x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; uint8_t x_344; lean_object* x_349; lean_object* x_361; lean_object* x_362; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_28 = lean_ctor_get(x_3, 2);
x_29 = lean_ctor_get(x_3, 3);
x_30 = lean_ctor_get(x_3, 4);
x_31 = lean_ctor_get(x_3, 5);
x_32 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_32);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_141 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_142);
x_143 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
x_361 = lean_task_get_own(x_141);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_349 = x_362;
goto block_360;
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
block_12:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_17 = lean_apply_1(x_16, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_9 = x_14;
x_10 = x_18;
goto block_12;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_17);
x_19 = lean_box(0);
x_9 = x_14;
x_10 = x_19;
goto block_12;
}
}
block_24:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_13 = x_21;
x_14 = x_23;
goto block_20;
}
block_55:
{
uint8_t x_46; 
x_46 = lean_nat_dec_lt(x_43, x_41);
lean_dec(x_43);
if (x_46 == 0)
{
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_32);
x_13 = x_44;
x_14 = x_40;
goto block_20;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_nat_dec_le(x_41, x_41);
if (x_48 == 0)
{
if (x_46 == 0)
{
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_32);
x_13 = x_44;
x_14 = x_40;
goto block_20;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_32, x_45, x_37, x_42, x_49, x_50, x_47, x_40);
lean_dec_ref(x_42);
x_21 = x_44;
x_22 = x_51;
goto block_24;
}
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(x_32, x_45, x_37, x_42, x_52, x_53, x_47, x_40);
lean_dec_ref(x_42);
x_21 = x_44;
x_22 = x_54;
goto block_24;
}
}
}
block_64:
{
if (x_57 == 0)
{
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_32);
x_13 = x_61;
x_14 = x_56;
goto block_20;
}
else
{
if (x_62 == 0)
{
x_40 = x_56;
x_41 = x_58;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_33;
goto block_55;
}
else
{
uint8_t x_63; 
x_63 = 0;
x_40 = x_56;
x_41 = x_58;
x_42 = x_59;
x_43 = x_60;
x_44 = x_61;
x_45 = x_63;
goto block_55;
}
}
}
block_128:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_127; 
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
x_77 = lean_ctor_get_uint8(x_66, sizeof(void*)*6);
x_78 = lean_ctor_get(x_66, 2);
x_79 = lean_ctor_get(x_66, 3);
x_80 = lean_ctor_get(x_66, 4);
x_81 = lean_ctor_get(x_66, 5);
x_127 = !lean_is_exclusive(x_66);
if (x_127 == 0)
{
x_82 = x_66;
x_83 = x_127;
goto block_126;
}
else
{
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_66);
x_82 = lean_box(0);
x_83 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_74, 4);
x_85 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (x_83 == 0)
{
lean_ctor_set(x_82, 3, x_85);
x_86 = x_82;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_125, 0, x_75);
lean_ctor_set(x_125, 1, x_76);
lean_ctor_set(x_125, 2, x_78);
lean_ctor_set(x_125, 3, x_85);
lean_ctor_set(x_125, 4, x_80);
lean_ctor_set(x_125, 5, x_81);
lean_ctor_set_uint8(x_125, sizeof(void*)*6, x_77);
x_86 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_string_append(x_79, x_73);
lean_dec_ref(x_73);
x_88 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
x_89 = lean_string_append(x_87, x_88);
lean_inc_ref(x_84);
lean_inc_ref(x_89);
x_90 = lean_apply_2(x_84, x_89, lean_box(0));
if (lean_obj_tag(x_90) == 0)
{
lean_dec_ref(x_90);
lean_dec_ref(x_89);
x_56 = x_86;
x_57 = x_65;
x_58 = x_68;
x_59 = x_69;
x_60 = x_70;
x_61 = x_71;
x_62 = x_72;
goto block_64;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_123; 
x_91 = lean_ctor_get(x_90, 0);
x_123 = !lean_is_exclusive(x_90);
if (x_123 == 0)
{
x_92 = x_90;
x_93 = x_123;
goto block_122;
}
else
{
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_94 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_95 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_96 = lean_unsigned_to_nat(89u);
x_97 = lean_unsigned_to_nat(4u);
x_98 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_99 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7));
x_100 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12));
lean_inc(x_70);
x_101 = l_Lean_Name_num___override(x_100, x_70);
x_102 = l_Lean_Name_str___override(x_101, x_99);
x_103 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15));
x_104 = l_Lean_Name_str___override(x_102, x_103);
x_105 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_104, x_67);
x_106 = lean_string_append(x_98, x_105);
lean_dec_ref(x_105);
x_107 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_io_error_to_string(x_91);
x_110 = lean_string_append(x_108, x_109);
lean_dec_ref(x_109);
x_111 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_112 = lean_string_append(x_110, x_111);
x_113 = l_String_quote(x_89);
if (x_93 == 0)
{
lean_ctor_set_tag(x_92, 3);
lean_ctor_set(x_92, 0, x_113);
x_114 = x_92;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_113);
x_114 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = l_Std_Format_defWidth;
lean_inc_n(x_70, 2);
x_116 = l_Std_Format_pretty(x_114, x_115, x_70, x_70);
x_117 = lean_string_append(x_112, x_116);
lean_dec_ref(x_116);
x_118 = l_mkPanicMessageWithDecl(x_94, x_95, x_96, x_97, x_117);
lean_dec_ref(x_117);
x_119 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_118);
x_56 = x_86;
x_57 = x_65;
x_58 = x_68;
x_59 = x_69;
x_60 = x_70;
x_61 = x_71;
x_62 = x_72;
goto block_64;
}
}
}
}
}
}
block_140:
{
lean_object* x_139; 
x_139 = l_Lake_Ansi_chalk(x_138, x_134);
lean_dec_ref(x_134);
lean_dec_ref(x_138);
x_65 = x_130;
x_66 = x_129;
x_67 = x_132;
x_68 = x_131;
x_69 = x_133;
x_70 = x_135;
x_71 = x_136;
x_72 = x_137;
x_73 = x_139;
goto block_128;
}
block_178:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_157 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_158 = lean_string_push(x_157, x_155);
x_159 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2));
x_160 = lean_string_append(x_158, x_159);
x_161 = l_Nat_reprFast(x_25);
x_162 = lean_string_append(x_160, x_161);
lean_dec_ref(x_161);
x_163 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3));
x_164 = lean_string_append(x_162, x_163);
x_165 = l_Nat_reprFast(x_26);
x_166 = lean_string_append(x_164, x_165);
lean_dec_ref(x_165);
x_167 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1));
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_string_append(x_168, x_148);
lean_dec_ref(x_148);
x_170 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2));
x_171 = lean_string_append(x_169, x_170);
x_172 = lean_string_append(x_171, x_152);
lean_dec_ref(x_152);
x_173 = lean_string_append(x_172, x_170);
x_174 = lean_string_append(x_173, x_142);
lean_dec_ref(x_142);
x_175 = lean_string_append(x_174, x_156);
lean_dec_ref(x_156);
if (x_37 == 0)
{
x_65 = x_144;
x_66 = x_150;
x_67 = x_145;
x_68 = x_151;
x_69 = x_146;
x_70 = x_153;
x_71 = x_154;
x_72 = x_149;
x_73 = x_175;
goto block_128;
}
else
{
if (x_144 == 0)
{
lean_object* x_176; 
x_176 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3));
x_129 = x_150;
x_130 = x_144;
x_131 = x_151;
x_132 = x_145;
x_133 = x_146;
x_134 = x_175;
x_135 = x_153;
x_136 = x_154;
x_137 = x_149;
x_138 = x_176;
goto block_140;
}
else
{
lean_object* x_177; 
x_177 = l_Lake_LogLevel_ansiColor(x_147);
x_129 = x_150;
x_130 = x_144;
x_131 = x_151;
x_132 = x_145;
x_133 = x_146;
x_134 = x_175;
x_135 = x_153;
x_136 = x_154;
x_137 = x_149;
x_138 = x_177;
goto block_140;
}
}
}
block_192:
{
lean_object* x_191; 
x_191 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_144 = x_179;
x_145 = x_180;
x_146 = x_181;
x_147 = x_182;
x_148 = x_183;
x_149 = x_184;
x_150 = x_185;
x_151 = x_186;
x_152 = x_187;
x_153 = x_188;
x_154 = x_189;
x_155 = x_190;
x_156 = x_191;
goto block_178;
}
block_212:
{
if (x_39 == 0)
{
lean_dec(x_199);
x_179 = x_193;
x_180 = x_194;
x_181 = x_195;
x_182 = x_196;
x_183 = x_205;
x_184 = x_197;
x_185 = x_198;
x_186 = x_200;
x_187 = x_201;
x_188 = x_202;
x_189 = x_203;
x_190 = x_204;
goto block_192;
}
else
{
uint8_t x_206; 
x_206 = lean_nat_dec_lt(x_202, x_199);
if (x_206 == 0)
{
lean_dec(x_199);
x_179 = x_193;
x_180 = x_194;
x_181 = x_195;
x_182 = x_196;
x_183 = x_205;
x_184 = x_197;
x_185 = x_198;
x_186 = x_200;
x_187 = x_201;
x_188 = x_202;
x_189 = x_203;
x_190 = x_204;
goto block_192;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4));
x_208 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(x_199);
x_209 = lean_string_append(x_207, x_208);
lean_dec_ref(x_208);
x_210 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5));
x_211 = lean_string_append(x_209, x_210);
x_144 = x_193;
x_145 = x_194;
x_146 = x_195;
x_147 = x_196;
x_148 = x_205;
x_149 = x_197;
x_150 = x_198;
x_151 = x_200;
x_152 = x_201;
x_153 = x_202;
x_154 = x_203;
x_155 = x_204;
x_156 = x_211;
goto block_178;
}
}
}
block_227:
{
if (x_143 == 0)
{
lean_object* x_225; 
x_225 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_193 = x_214;
x_194 = x_217;
x_195 = x_219;
x_196 = x_218;
x_197 = x_223;
x_198 = x_213;
x_199 = x_215;
x_200 = x_216;
x_201 = x_220;
x_202 = x_221;
x_203 = x_222;
x_204 = x_224;
x_205 = x_225;
goto block_212;
}
else
{
lean_object* x_226; 
x_226 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6));
x_193 = x_214;
x_194 = x_217;
x_195 = x_219;
x_196 = x_218;
x_197 = x_223;
x_198 = x_213;
x_199 = x_215;
x_200 = x_216;
x_201 = x_220;
x_202 = x_221;
x_203 = x_222;
x_204 = x_224;
x_205 = x_226;
goto block_212;
}
}
block_243:
{
if (x_230 == 0)
{
if (x_38 == 0)
{
lean_dec_ref(x_237);
lean_dec(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_142);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
x_5 = x_229;
goto block_8;
}
else
{
if (x_37 == 0)
{
if (x_228 == 0)
{
lean_dec_ref(x_237);
lean_dec(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_142);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
x_5 = x_229;
goto block_8;
}
else
{
lean_object* x_239; uint32_t x_240; 
x_239 = l_Lake_JobAction_verb(x_238, x_231);
x_240 = 10004;
x_213 = x_229;
x_214 = x_230;
x_215 = x_232;
x_216 = x_233;
x_217 = x_228;
x_218 = x_235;
x_219 = x_234;
x_220 = x_239;
x_221 = x_236;
x_222 = x_237;
x_223 = x_238;
x_224 = x_240;
goto block_227;
}
}
else
{
lean_dec_ref(x_237);
lean_dec(x_236);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_142);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
x_5 = x_229;
goto block_8;
}
}
}
else
{
lean_object* x_241; uint32_t x_242; 
x_241 = l_Lake_JobAction_verb(x_238, x_231);
x_242 = l_Lake_LogLevel_icon(x_235);
x_213 = x_229;
x_214 = x_230;
x_215 = x_232;
x_216 = x_233;
x_217 = x_230;
x_218 = x_235;
x_219 = x_234;
x_220 = x_241;
x_221 = x_236;
x_222 = x_237;
x_223 = x_238;
x_224 = x_242;
goto block_227;
}
}
block_255:
{
if (x_143 == 0)
{
x_228 = x_244;
x_229 = x_245;
x_230 = x_254;
x_231 = x_246;
x_232 = x_247;
x_233 = x_248;
x_234 = x_249;
x_235 = x_250;
x_236 = x_251;
x_237 = x_252;
x_238 = x_253;
goto block_243;
}
else
{
if (x_36 == 0)
{
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_142);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
x_5 = x_245;
goto block_8;
}
else
{
x_228 = x_244;
x_229 = x_245;
x_230 = x_254;
x_231 = x_246;
x_232 = x_247;
x_233 = x_248;
x_234 = x_249;
x_235 = x_250;
x_236 = x_251;
x_237 = x_252;
x_238 = x_253;
goto block_243;
}
}
}
block_283:
{
if (x_265 == 0)
{
if (x_263 == 0)
{
x_244 = x_256;
x_245 = x_267;
x_246 = x_257;
x_247 = x_258;
x_248 = x_260;
x_249 = x_261;
x_250 = x_262;
x_251 = x_264;
x_252 = x_266;
x_253 = x_265;
x_254 = x_263;
goto block_255;
}
else
{
x_244 = x_256;
x_245 = x_267;
x_246 = x_257;
x_247 = x_258;
x_248 = x_260;
x_249 = x_261;
x_250 = x_262;
x_251 = x_264;
x_252 = x_266;
x_253 = x_265;
x_254 = x_259;
goto block_255;
}
}
else
{
if (x_143 == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_282; 
x_268 = lean_ctor_get(x_267, 0);
x_269 = lean_ctor_get(x_267, 1);
x_270 = lean_ctor_get_uint8(x_267, sizeof(void*)*6);
x_271 = lean_ctor_get(x_267, 2);
x_272 = lean_ctor_get(x_267, 3);
x_273 = lean_ctor_get(x_267, 4);
x_274 = lean_ctor_get(x_267, 5);
x_282 = !lean_is_exclusive(x_267);
if (x_282 == 0)
{
x_275 = x_267;
x_276 = x_282;
goto block_281;
}
else
{
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_267);
x_275 = lean_box(0);
x_276 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_277; lean_object* x_278; 
lean_inc_ref(x_142);
x_277 = lean_array_push(x_271, x_142);
if (x_276 == 0)
{
lean_ctor_set(x_275, 2, x_277);
x_278 = x_275;
goto block_279;
}
else
{
lean_object* x_280; 
x_280 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_280, 0, x_268);
lean_ctor_set(x_280, 1, x_269);
lean_ctor_set(x_280, 2, x_277);
lean_ctor_set(x_280, 3, x_272);
lean_ctor_set(x_280, 4, x_273);
lean_ctor_set(x_280, 5, x_274);
lean_ctor_set_uint8(x_280, sizeof(void*)*6, x_270);
x_278 = x_280;
goto block_279;
}
block_279:
{
x_244 = x_256;
x_245 = x_278;
x_246 = x_257;
x_247 = x_258;
x_248 = x_260;
x_249 = x_261;
x_250 = x_262;
x_251 = x_264;
x_252 = x_266;
x_253 = x_265;
x_254 = x_265;
goto block_255;
}
}
}
else
{
x_244 = x_256;
x_245 = x_267;
x_246 = x_257;
x_247 = x_258;
x_248 = x_260;
x_249 = x_261;
x_250 = x_262;
x_251 = x_264;
x_252 = x_266;
x_253 = x_265;
x_254 = x_265;
goto block_255;
}
}
}
block_308:
{
if (x_291 == 0)
{
x_256 = x_294;
x_257 = x_284;
x_258 = x_285;
x_259 = x_286;
x_260 = x_287;
x_261 = x_288;
x_262 = x_289;
x_263 = x_290;
x_264 = x_292;
x_265 = x_293;
x_266 = x_2;
x_267 = x_3;
goto block_283;
}
else
{
if (x_27 == 0)
{
lean_object* x_295; uint8_t x_296; uint8_t x_301; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc_ref(x_28);
x_301 = !lean_is_exclusive(x_3);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_3, 5);
lean_dec(x_302);
x_303 = lean_ctor_get(x_3, 4);
lean_dec(x_303);
x_304 = lean_ctor_get(x_3, 3);
lean_dec(x_304);
x_305 = lean_ctor_get(x_3, 2);
lean_dec(x_305);
x_306 = lean_ctor_get(x_3, 1);
lean_dec(x_306);
x_307 = lean_ctor_get(x_3, 0);
lean_dec(x_307);
x_295 = x_3;
x_296 = x_301;
goto block_300;
}
else
{
lean_dec(x_3);
x_295 = lean_box(0);
x_296 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_297; 
lean_inc(x_26);
lean_inc(x_25);
if (x_296 == 0)
{
x_297 = x_295;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_299, 0, x_25);
lean_ctor_set(x_299, 1, x_26);
lean_ctor_set(x_299, 2, x_28);
lean_ctor_set(x_299, 3, x_29);
lean_ctor_set(x_299, 4, x_30);
lean_ctor_set(x_299, 5, x_31);
x_297 = x_299;
goto block_298;
}
block_298:
{
lean_ctor_set_uint8(x_297, sizeof(void*)*6, x_291);
x_256 = x_294;
x_257 = x_284;
x_258 = x_285;
x_259 = x_286;
x_260 = x_287;
x_261 = x_288;
x_262 = x_289;
x_263 = x_290;
x_264 = x_292;
x_265 = x_293;
x_266 = x_2;
x_267 = x_297;
goto block_283;
}
}
}
else
{
x_256 = x_294;
x_257 = x_284;
x_258 = x_285;
x_259 = x_286;
x_260 = x_287;
x_261 = x_288;
x_262 = x_289;
x_263 = x_290;
x_264 = x_292;
x_265 = x_293;
x_266 = x_2;
x_267 = x_3;
goto block_283;
}
}
}
block_322:
{
uint8_t x_319; 
x_319 = l_Lake_instOrdJobAction_ord(x_35, x_309);
if (x_319 == 2)
{
uint8_t x_320; 
x_320 = 0;
x_284 = x_309;
x_285 = x_310;
x_286 = x_318;
x_287 = x_311;
x_288 = x_313;
x_289 = x_312;
x_290 = x_314;
x_291 = x_315;
x_292 = x_316;
x_293 = x_317;
x_294 = x_320;
goto block_308;
}
else
{
uint8_t x_321; 
x_321 = 1;
x_284 = x_309;
x_285 = x_310;
x_286 = x_318;
x_287 = x_311;
x_288 = x_313;
x_289 = x_312;
x_290 = x_314;
x_291 = x_315;
x_292 = x_316;
x_293 = x_317;
x_294 = x_321;
goto block_308;
}
}
block_336:
{
uint8_t x_332; uint8_t x_333; 
x_332 = lean_strict_and(x_328, x_331);
x_333 = l_Lake_instOrdLogLevel_ord(x_33, x_327);
if (x_333 == 2)
{
uint8_t x_334; 
x_334 = 0;
x_309 = x_323;
x_310 = x_324;
x_311 = x_325;
x_312 = x_327;
x_313 = x_326;
x_314 = x_328;
x_315 = x_329;
x_316 = x_330;
x_317 = x_332;
x_318 = x_334;
goto block_322;
}
else
{
uint8_t x_335; 
x_335 = 1;
x_309 = x_323;
x_310 = x_324;
x_311 = x_325;
x_312 = x_327;
x_313 = x_326;
x_314 = x_328;
x_315 = x_329;
x_316 = x_330;
x_317 = x_332;
x_318 = x_335;
goto block_322;
}
}
block_348:
{
uint8_t x_345; 
x_345 = l_Lake_instOrdLogLevel_ord(x_34, x_340);
if (x_345 == 2)
{
uint8_t x_346; 
x_346 = 0;
x_323 = x_337;
x_324 = x_338;
x_325 = x_339;
x_326 = x_341;
x_327 = x_340;
x_328 = x_344;
x_329 = x_342;
x_330 = x_343;
x_331 = x_346;
goto block_336;
}
else
{
uint8_t x_347; 
x_347 = 1;
x_323 = x_337;
x_324 = x_338;
x_325 = x_339;
x_326 = x_341;
x_327 = x_340;
x_328 = x_344;
x_329 = x_342;
x_330 = x_343;
x_331 = x_347;
goto block_336;
}
}
block_360:
{
lean_object* x_350; uint8_t x_351; uint8_t x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc_ref(x_350);
x_351 = lean_ctor_get_uint8(x_349, sizeof(void*)*3);
x_352 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 1);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
lean_dec_ref(x_349);
x_354 = l_Lake_Log_maxLv(x_350);
x_355 = lean_array_get_size(x_350);
x_356 = lean_unsigned_to_nat(0u);
x_357 = lean_nat_dec_eq(x_355, x_356);
if (x_357 == 0)
{
uint8_t x_358; 
x_358 = 1;
x_337 = x_351;
x_338 = x_353;
x_339 = x_355;
x_340 = x_354;
x_341 = x_350;
x_342 = x_352;
x_343 = x_356;
x_344 = x_358;
goto block_348;
}
else
{
uint8_t x_359; 
x_359 = 0;
x_337 = x_351;
x_338 = x_353;
x_339 = x_355;
x_340 = x_354;
x_341 = x_350;
x_342 = x_352;
x_343 = x_356;
x_344 = x_359;
goto block_348;
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
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_array_uget_borrowed(x_1, x_2);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_io_get_task_state(x_18);
switch (x_19) {
case 0:
{
lean_object* x_20; uint8_t x_21; uint8_t x_27; 
lean_inc(x_16);
lean_inc(x_15);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_4, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_dec(x_29);
x_20 = x_4;
x_21 = x_27;
goto block_26;
}
else
{
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_17);
x_22 = lean_array_push(x_16, x_17);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_22);
x_23 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
x_8 = x_23;
x_9 = x_6;
goto block_13;
}
}
}
case 1:
{
lean_object* x_30; uint8_t x_31; uint8_t x_38; 
lean_inc(x_16);
lean_inc(x_15);
x_38 = !lean_is_exclusive(x_4);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_4, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_4, 0);
lean_dec(x_40);
x_30 = x_4;
x_31 = x_38;
goto block_37;
}
else
{
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_17);
x_32 = lean_array_push(x_15, x_17);
lean_inc(x_17);
x_33 = lean_array_push(x_16, x_17);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_33);
lean_ctor_set(x_30, 0, x_32);
x_34 = x_30;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
x_8 = x_34;
x_9 = x_6;
goto block_13;
}
}
}
default: 
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_58; 
lean_inc_ref(x_5);
lean_inc(x_17);
x_41 = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(x_17, x_5, x_6);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_42, 1);
x_45 = lean_ctor_get_uint8(x_42, sizeof(void*)*6);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get(x_42, 3);
x_48 = lean_ctor_get(x_42, 4);
x_49 = lean_ctor_get(x_42, 5);
x_58 = !lean_is_exclusive(x_42);
if (x_58 == 0)
{
x_50 = x_42;
x_51 = x_58;
goto block_57;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_50 = lean_box(0);
x_51 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_43, x_52);
lean_dec(x_43);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_53);
x_54 = x_50;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*6, x_45);
x_54 = x_56;
goto block_55;
}
block_55:
{
x_8 = x_4;
x_9 = x_54;
goto block_13;
}
}
}
}
}
else
{
lean_object* x_59; 
lean_dec_ref(x_5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_6);
return x_59;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Monitor_poll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_53; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_st_ref_take(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
x_9 = lean_st_ref_set(x_5, x_8);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
x_16 = lean_ctor_get(x_3, 5);
x_53 = !lean_is_exclusive(x_3);
if (x_53 == 0)
{
x_17 = x_3;
x_18 = x_53;
goto block_52;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_32; lean_object* x_36; lean_object* x_37; 
x_19 = lean_array_get_size(x_6);
x_36 = lean_nat_add(x_11, x_19);
lean_dec(x_11);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_36);
x_37 = x_17;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_13);
lean_ctor_set(x_51, 3, x_14);
lean_ctor_set(x_51, 4, x_15);
lean_ctor_set(x_51, 5, x_16);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_12);
x_37 = x_51;
goto block_50;
}
block_31:
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_7, x_19);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_20;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_19, x_19);
if (x_24 == 0)
{
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_20;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec_ref(x_20);
x_25 = 0;
x_26 = lean_usize_of_nat(x_19);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_25, x_26, x_21, x_2, x_22);
lean_dec(x_6);
return x_27;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
lean_dec_ref(x_20);
x_28 = 0;
x_29 = lean_usize_of_nat(x_19);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_6, x_28, x_29, x_21, x_2, x_22);
lean_dec(x_6);
return x_30;
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_20 = x_32;
x_21 = x_33;
x_22 = x_34;
goto block_31;
}
block_50:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0, &l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Monitor_poll___closed__0);
x_39 = lean_array_get_size(x_1);
x_40 = lean_nat_dec_lt(x_7, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc_ref(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_37);
x_20 = x_41;
x_21 = x_38;
x_22 = x_37;
goto block_31;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_39, x_39);
if (x_42 == 0)
{
if (x_40 == 0)
{
lean_object* x_43; 
lean_inc_ref(x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_37);
x_20 = x_43;
x_21 = x_38;
x_22 = x_37;
goto block_31;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_39);
lean_inc_ref(x_2);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_44, x_45, x_38, x_2, x_37);
x_32 = x_46;
goto block_35;
}
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_39);
lean_inc_ref(x_2);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_poll_spec__0(x_1, x_47, x_48, x_38, x_2, x_37);
x_32 = x_49;
goto block_35;
}
}
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
lean_object* x_4; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_io_mono_ms_now();
x_24 = lean_ctor_get(x_2, 4);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_27 = lean_nat_sub(x_25, x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
x_4 = x_2;
goto block_22;
}
else
{
uint32_t x_30; lean_object* x_31; 
x_30 = lean_uint32_of_nat(x_27);
lean_dec(x_27);
x_31 = l_IO_sleep(x_30);
x_4 = x_2;
goto block_22;
}
block_22:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_5 = lean_io_mono_ms_now();
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 5);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_4, 4);
lean_dec(x_21);
x_12 = x_4;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set(x_12, 4, x_5);
x_15 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_10);
lean_ctor_set(x_18, 4, x_5);
lean_ctor_set(x_18, 5, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*6, x_8);
x_15 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_25; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_poll(x_1, x_2, x_3);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
x_10 = x_6;
x_11 = x_25;
goto block_24;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_9);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
x_15 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 0, x_15);
x_16 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_7);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_del_object(x_10);
lean_inc_ref(x_2);
x_19 = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(x_8, x_9, x_2, x_7);
lean_dec(x_8);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(x_2, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_1 = x_9;
x_3 = x_22;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_66; 
lean_inc_ref(x_2);
x_5 = l___private_Lake_Build_Run_0__Lake_Monitor_loop(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 1);
x_66 = !lean_is_exclusive(x_5);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_5, 0);
lean_dec(x_67);
x_7 = x_5;
x_8 = x_66;
goto block_65;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_64; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_12 = lean_ctor_get(x_6, 2);
x_13 = lean_ctor_get(x_6, 3);
x_14 = lean_ctor_get(x_6, 4);
x_15 = lean_ctor_get(x_6, 5);
x_64 = !lean_is_exclusive(x_6);
if (x_64 == 0)
{
x_16 = x_6;
x_17 = x_64;
goto block_63;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
if (x_17 == 0)
{
lean_ctor_set(x_16, 3, x_18);
x_19 = x_16;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_62, 0, x_9);
lean_ctor_set(x_62, 1, x_10);
lean_ctor_set(x_62, 2, x_12);
lean_ctor_set(x_62, 3, x_18);
lean_ctor_set(x_62, 4, x_14);
lean_ctor_set(x_62, 5, x_15);
lean_ctor_set_uint8(x_62, sizeof(void*)*6, x_11);
x_19 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_20; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_string_utf8_byte_size(x_13);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_35; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_30);
lean_dec_ref(x_28);
lean_inc_ref(x_13);
x_35 = lean_apply_2(x_30, x_13, lean_box(0));
if (lean_obj_tag(x_35) == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_13);
goto block_34;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_58; 
x_36 = lean_ctor_get(x_35, 0);
x_58 = !lean_is_exclusive(x_35);
if (x_58 == 0)
{
x_37 = x_35;
x_38 = x_58;
goto block_57;
}
else
{
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_40 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_41 = lean_unsigned_to_nat(89u);
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_44 = lean_io_error_to_string(x_36);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_47 = lean_string_append(x_45, x_46);
x_48 = l_String_quote(x_13);
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 3);
lean_ctor_set(x_37, 0, x_48);
x_49 = x_37;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_48);
x_49 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l_Std_Format_defWidth;
x_51 = l_Std_Format_pretty(x_49, x_50, x_26, x_26);
x_52 = lean_string_append(x_47, x_51);
lean_dec_ref(x_51);
x_53 = l_mkPanicMessageWithDecl(x_39, x_40, x_41, x_42, x_52);
lean_dec_ref(x_52);
x_54 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_53);
goto block_34;
}
}
}
block_34:
{
lean_object* x_31; 
x_31 = lean_apply_1(x_29, lean_box(0));
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_20 = x_32;
goto block_24;
}
else
{
lean_object* x_33; 
lean_dec_ref(x_31);
x_33 = lean_box(0);
x_20 = x_33;
goto block_24;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_13);
lean_del_object(x_7);
lean_dec_ref(x_2);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_19);
return x_60;
}
block_24:
{
lean_object* x_21; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_20);
x_21 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_19);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
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
static uint32_t _init_l_Lake_noBuildCode(void) {
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3);
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7);
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11);
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; lean_object* x_27; uint8_t x_117; 
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed), 4, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__0, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
x_117 = l_Lake_Workspace_isRootArtifactCacheWritable(x_2);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_2, 0);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = l_Lean_Name_toString(x_119, x_117);
x_121 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
x_122 = lean_string_append(x_120, x_121);
x_123 = 2;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_apply_2(x_1, x_124, lean_box(0));
goto block_116;
}
else
{
lean_dec_ref(x_1);
goto block_116;
}
block_8:
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
block_25:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_12);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_11, x_13);
if (x_15 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_9);
return x_14;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
if (x_15 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_9);
return x_14;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_10, x_9, x_12, x_17, x_18, x_14);
x_20 = lean_apply_1(x_19, lean_box(0));
return x_20;
}
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_13);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_10, x_9, x_12, x_21, x_22, x_14);
x_24 = lean_apply_1(x_23, lean_box(0));
return x_24;
}
}
}
block_41:
{
if (x_5 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
lean_dec_ref(x_9);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_array_get_size(x_27);
x_30 = lean_box(0);
x_31 = lean_nat_dec_lt(x_26, x_29);
if (x_31 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_9);
return x_30;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_29, x_29);
if (x_32 == 0)
{
if (x_31 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_9);
return x_30;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_29);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_10, x_9, x_27, x_33, x_34, x_30);
x_36 = lean_apply_1(x_35, lean_box(0));
return x_36;
}
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_29);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_10, x_9, x_27, x_37, x_38, x_30);
x_40 = lean_apply_1(x_39, lean_box(0));
return x_40;
}
}
}
}
block_116:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_42);
lean_dec_ref(x_2);
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
x_47 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
x_48 = l_Lake_CacheMap_writeFile(x_4, x_45, x_47);
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
if (x_5 == 0)
{
lean_dec(x_49);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
goto block_8;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_52);
lean_dec_ref(x_3);
x_53 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
x_54 = lean_apply_2(x_52, x_53, lean_box(0));
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_11 = x_46;
x_12 = x_49;
goto block_25;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
x_57 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_58 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_59 = lean_unsigned_to_nat(89u);
x_60 = lean_unsigned_to_nat(4u);
x_61 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_62 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_63 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_62, x_5);
x_64 = lean_string_append(x_61, x_63);
lean_dec_ref(x_63);
x_65 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_io_error_to_string(x_55);
x_68 = lean_string_append(x_66, x_67);
lean_dec_ref(x_67);
x_69 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
x_72 = lean_string_append(x_70, x_71);
x_73 = l_mkPanicMessageWithDecl(x_57, x_58, x_59, x_60, x_72);
lean_dec_ref(x_72);
x_74 = l_panic___redArg(x_56, x_73);
x_75 = lean_apply_1(x_74, lean_box(0));
x_11 = x_46;
x_12 = x_49;
goto block_25;
}
}
}
else
{
lean_dec(x_49);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
goto block_8;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_dec_ref(x_48);
x_77 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_77);
lean_dec_ref(x_3);
x_78 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
x_79 = lean_apply_2(x_77, x_78, lean_box(0));
if (lean_obj_tag(x_79) == 0)
{
lean_dec_ref(x_79);
x_26 = x_46;
x_27 = x_76;
goto block_41;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
x_82 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_83 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_84 = lean_unsigned_to_nat(89u);
x_85 = lean_unsigned_to_nat(4u);
x_86 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_87 = lean_io_error_to_string(x_80);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
x_92 = lean_string_append(x_90, x_91);
x_93 = l_mkPanicMessageWithDecl(x_82, x_83, x_84, x_85, x_92);
lean_dec_ref(x_92);
x_94 = l_panic___redArg(x_81, x_93);
x_95 = lean_apply_1(x_94, lean_box(0));
x_26 = x_46;
x_27 = x_76;
goto block_41;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_43);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
x_96 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_96);
lean_dec_ref(x_3);
x_97 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
x_98 = lean_apply_2(x_96, x_97, lean_box(0));
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec_ref(x_98);
x_101 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__1, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__1);
x_102 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_103 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_104 = lean_unsigned_to_nat(89u);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_107 = lean_io_error_to_string(x_100);
x_108 = lean_string_append(x_106, x_107);
lean_dec_ref(x_107);
x_109 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
x_112 = lean_string_append(x_110, x_111);
x_113 = l_mkPanicMessageWithDecl(x_102, x_103, x_104, x_105, x_112);
lean_dec_ref(x_112);
x_114 = l_panic___redArg(x_101, x_113);
x_115 = lean_apply_1(x_114, lean_box(0));
return x_115;
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
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_array_uget_borrowed(x_2, x_3);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0));
x_16 = lean_string_append(x_15, x_14);
x_17 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0));
x_18 = lean_string_append(x_16, x_17);
lean_inc_ref(x_13);
lean_inc_ref(x_18);
x_19 = lean_apply_2(x_13, x_18, lean_box(0));
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_7 = x_20;
goto block_11;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_44; 
x_21 = lean_ctor_get(x_19, 0);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
x_22 = x_19;
x_23 = x_44;
goto block_43;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_25 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_26 = lean_unsigned_to_nat(89u);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_30 = lean_io_error_to_string(x_21);
x_31 = lean_string_append(x_29, x_30);
lean_dec_ref(x_30);
x_32 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_33 = lean_string_append(x_31, x_32);
x_34 = l_String_quote(x_18);
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 0, x_34);
x_35 = x_22;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_34);
x_35 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Std_Format_defWidth;
x_37 = l_Std_Format_pretty(x_35, x_36, x_28, x_28);
x_38 = lean_string_append(x_33, x_37);
lean_dec_ref(x_37);
x_39 = l_mkPanicMessageWithDecl(x_24, x_25, x_26, x_27, x_38);
lean_dec_ref(x_38);
x_40 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_39);
x_7 = x_40;
goto block_11;
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
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
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
x_2 = l_String_quote(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__6, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Format_defWidth;
x_3 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__7, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7);
x_4 = l_Std_Format_pretty(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_reportResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_81 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
lean_dec_ref(x_3);
x_92 = lean_array_get_size(x_81);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_101; lean_object* x_113; lean_object* x_114; 
lean_dec(x_82);
x_95 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_2, 4);
x_113 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5));
lean_inc_ref(x_96);
x_114 = lean_apply_2(x_96, x_113, lean_box(0));
if (lean_obj_tag(x_114) == 0)
{
lean_dec_ref(x_114);
goto block_112;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_117 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_118 = lean_unsigned_to_nat(89u);
x_119 = lean_unsigned_to_nat(4u);
x_120 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_121 = lean_io_error_to_string(x_115);
x_122 = lean_string_append(x_120, x_121);
lean_dec_ref(x_121);
x_123 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_reportResult___closed__8, &l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
x_126 = lean_string_append(x_124, x_125);
x_127 = l_mkPanicMessageWithDecl(x_116, x_117, x_118, x_119, x_126);
lean_dec_ref(x_126);
x_128 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_127);
goto block_112;
}
block_100:
{
lean_object* x_97; 
x_97 = lean_apply_1(x_95, lean_box(0));
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
return x_98;
}
else
{
lean_object* x_99; 
lean_dec_ref(x_97);
x_99 = lean_box(0);
return x_99;
}
}
block_102:
{
goto block_100;
}
block_112:
{
uint8_t x_103; 
x_103 = lean_nat_dec_lt(x_93, x_92);
if (x_103 == 0)
{
lean_dec_ref(x_81);
lean_dec_ref(x_2);
goto block_100;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_box(0);
x_105 = lean_nat_dec_le(x_92, x_92);
if (x_105 == 0)
{
if (x_103 == 0)
{
lean_dec_ref(x_81);
lean_dec_ref(x_2);
goto block_100;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_92);
x_108 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(x_2, x_81, x_106, x_107, x_104);
lean_dec_ref(x_81);
x_101 = x_108;
goto block_102;
}
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; 
x_109 = 0;
x_110 = lean_usize_of_nat(x_92);
x_111 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(x_2, x_81, x_109, x_110, x_104);
lean_dec_ref(x_81);
x_101 = x_111;
goto block_102;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec_ref(x_81);
x_129 = l_Lake_BuildConfig_showProgress(x_1);
if (x_129 == 0)
{
x_83 = x_129;
goto block_91;
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_83 = x_130;
goto block_91;
}
}
block_80:
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
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_43; 
x_15 = lean_ctor_get(x_13, 0);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
x_16 = x_13;
x_17 = x_43;
goto block_42;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_19 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_20 = lean_unsigned_to_nat(89u);
x_21 = lean_unsigned_to_nat(4u);
x_22 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_23 = lean_unsigned_to_nat(0u);
x_24 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_25 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_24, x_5);
x_26 = lean_string_append(x_22, x_25);
lean_dec_ref(x_25);
x_27 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_io_error_to_string(x_15);
x_30 = lean_string_append(x_28, x_29);
lean_dec_ref(x_29);
x_31 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_32 = lean_string_append(x_30, x_31);
x_33 = l_String_quote(x_12);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_33);
x_34 = x_16;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_33);
x_34 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Std_Format_defWidth;
x_36 = l_Std_Format_pretty(x_34, x_35, x_23, x_23);
x_37 = lean_string_append(x_32, x_36);
lean_dec_ref(x_36);
x_38 = l_mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_37);
lean_dec_ref(x_37);
x_39 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_44);
lean_dec_ref(x_2);
x_45 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2));
x_46 = lean_string_append(x_45, x_6);
lean_dec_ref(x_6);
x_47 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1));
x_48 = lean_string_append(x_46, x_47);
lean_inc_ref(x_48);
x_49 = lean_apply_2(x_44, x_48, lean_box(0));
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec_ref(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_79; 
x_51 = lean_ctor_get(x_49, 0);
x_79 = !lean_is_exclusive(x_49);
if (x_79 == 0)
{
x_52 = x_49;
x_53 = x_79;
goto block_78;
}
else
{
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_55 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_56 = lean_unsigned_to_nat(89u);
x_57 = lean_unsigned_to_nat(4u);
x_58 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_59 = lean_unsigned_to_nat(0u);
x_60 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_61 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_60, x_7);
x_62 = lean_string_append(x_58, x_61);
lean_dec_ref(x_61);
x_63 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_io_error_to_string(x_51);
x_66 = lean_string_append(x_64, x_65);
lean_dec_ref(x_65);
x_67 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_68 = lean_string_append(x_66, x_67);
x_69 = l_String_quote(x_48);
if (x_53 == 0)
{
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_69);
x_70 = x_52;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_69);
x_70 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = l_Std_Format_defWidth;
x_72 = l_Std_Format_pretty(x_70, x_71, x_59, x_59);
x_73 = lean_string_append(x_68, x_72);
lean_dec_ref(x_72);
x_74 = l_mkPanicMessageWithDecl(x_54, x_55, x_56, x_57, x_73);
lean_dec_ref(x_73);
x_75 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_74);
return x_75;
}
}
}
}
}
block_91:
{
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_dec_ref(x_2);
x_84 = lean_box(0);
return x_84;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_dec_eq(x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = l_Nat_reprFast(x_82);
x_88 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3));
x_89 = lean_string_append(x_87, x_88);
x_5 = x_83;
x_6 = x_89;
goto block_80;
}
else
{
lean_object* x_90; 
lean_dec(x_82);
x_90 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4));
x_5 = x_83;
x_6 = x_90;
goto block_80;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc_ref(x_2);
x_4 = l_Lake_Job_toOpaque___redArg(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_push(x_6, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0));
x_10 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1));
x_11 = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(x_1, x_7, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec_ref(x_12);
x_14 = lean_nat_dec_eq(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_2);
x_15 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2));
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_io_wait(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_18, 1);
lean_dec(x_28);
x_20 = x_18;
x_21 = x_27;
goto block_26;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_22);
lean_ctor_set(x_20, 0, x_11);
x_23 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_18, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_18, 0);
lean_dec(x_38);
x_29 = x_18;
x_30 = x_36;
goto block_35;
}
else
{
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4));
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_11);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_Env_leanGithash(x_4);
x_6 = l_Lake_Hash_nil;
x_7 = lean_string_hash(x_5);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_obj_once(&l_Lake_mkBuildContext___closed__4, &l_Lake_mkBuildContext___closed__4_once, _init_l_Lake_mkBuildContext___closed__4);
x_10 = lean_string_append(x_9, x_5);
lean_dec_ref(x_5);
x_11 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0));
x_12 = lean_obj_once(&l_Lake_mkBuildContext___closed__6, &l_Lake_mkBuildContext___closed__6_once, _init_l_Lake_mkBuildContext___closed__6);
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_42; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 1);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_14 = x_7;
x_15 = x_42;
goto block_41;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_9);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_16; 
x_16 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_9, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_28; 
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
x_19 = x_16;
x_20 = x_28;
goto block_27;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_21; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_18);
x_21 = x_14;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_26, 2, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_11);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_40; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
x_31 = x_16;
x_32 = x_40;
goto block_39;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_33; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_30);
x_33 = x_14;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_12);
lean_ctor_set(x_38, 2, x_13);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_11);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_33);
x_34 = x_31;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
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
x_10 = lean_array_uget_borrowed(x_4, x_5);
lean_inc_ref(x_1);
x_11 = l_Lake_logToStream(x_10, x_1, x_2, x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_24; lean_object* x_25; uint8_t x_107; 
x_107 = l_Lake_Workspace_isRootArtifactCacheWritable(x_4);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_4, 0);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
x_110 = l_Lean_Name_toString(x_109, x_107);
x_111 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13));
x_112 = lean_string_append(x_110, x_111);
x_113 = 2;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
lean_inc_ref(x_1);
x_115 = l_Lake_logToStream(x_114, x_1, x_2, x_3);
lean_dec_ref(x_114);
goto block_106;
}
else
{
goto block_106;
}
block_10:
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
block_23:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_11);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_12, x_13);
if (x_15 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_14;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
if (x_15 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_14;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_11, x_17, x_18, x_14);
lean_dec_ref(x_11);
return x_19;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_13);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_11, x_20, x_21, x_14);
lean_dec_ref(x_11);
return x_22;
}
}
}
block_37:
{
if (x_7 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_24);
x_28 = lean_box(0);
x_29 = lean_nat_dec_lt(x_25, x_27);
if (x_29 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_1);
return x_28;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
if (x_29 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_1);
return x_28;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_27);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_24, x_31, x_32, x_28);
lean_dec_ref(x_24);
return x_33;
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_27);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0_spec__0(x_1, x_2, x_3, x_24, x_34, x_35, x_28);
lean_dec_ref(x_24);
return x_36;
}
}
}
}
block_106:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_38);
lean_dec_ref(x_4);
x_39 = lean_ctor_get(x_38, 23);
lean_inc(x_39);
lean_dec_ref(x_38);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_st_ref_get(x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0));
x_44 = l_Lake_CacheMap_writeFile(x_6, x_41, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_eq(x_46, x_42);
if (x_47 == 0)
{
if (x_7 == 0)
{
lean_dec(x_45);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_48);
lean_dec_ref(x_5);
x_49 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1));
x_50 = lean_apply_2(x_48, x_49, lean_box(0));
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
x_11 = x_45;
x_12 = x_42;
goto block_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_53 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_54 = lean_unsigned_to_nat(89u);
x_55 = lean_unsigned_to_nat(4u);
x_56 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4));
x_57 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16));
x_58 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_57, x_7);
x_59 = lean_string_append(x_56, x_58);
lean_dec_ref(x_58);
x_60 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__19));
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_io_error_to_string(x_51);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4);
x_67 = lean_string_append(x_65, x_66);
x_68 = l_mkPanicMessageWithDecl(x_52, x_53, x_54, x_55, x_67);
lean_dec_ref(x_67);
x_69 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_68);
x_11 = x_45;
x_12 = x_42;
goto block_23;
}
}
}
else
{
lean_dec(x_45);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
goto block_10;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_dec_ref(x_44);
x_71 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_71);
lean_dec_ref(x_5);
x_72 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5));
x_73 = lean_apply_2(x_71, x_72, lean_box(0));
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_24 = x_70;
x_25 = x_42;
goto block_37;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_76 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_77 = lean_unsigned_to_nat(89u);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_80 = lean_io_error_to_string(x_74);
x_81 = lean_string_append(x_79, x_80);
lean_dec_ref(x_80);
x_82 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8);
x_85 = lean_string_append(x_83, x_84);
x_86 = l_mkPanicMessageWithDecl(x_75, x_76, x_77, x_78, x_85);
lean_dec_ref(x_85);
x_87 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_86);
x_24 = x_70;
x_25 = x_42;
goto block_37;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_39);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_88);
lean_dec_ref(x_5);
x_89 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9));
x_90 = lean_apply_2(x_88, x_89, lean_box(0));
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2));
x_94 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3));
x_95 = lean_unsigned_to_nat(89u);
x_96 = lean_unsigned_to_nat(4u);
x_97 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_print_x21___closed__20, &l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_once, _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__20);
x_98 = lean_io_error_to_string(x_92);
x_99 = lean_string_append(x_97, x_98);
lean_dec_ref(x_98);
x_100 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_print_x21___closed__21));
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_obj_once(&l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12, &l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12);
x_103 = lean_string_append(x_101, x_102);
x_104 = l_mkPanicMessageWithDecl(x_93, x_94, x_95, x_96, x_103);
lean_dec_ref(x_103);
x_105 = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(x_104);
return x_105;
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
static uint8_t _init_l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0(void) {
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
lean_object* x_6; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_4);
lean_inc_ref(x_13);
lean_inc_ref(x_10);
x_15 = l___private_Lake_Build_Run_0__Lake_reportResult(x_2, x_10, x_13);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec_ref(x_2);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
lean_dec_ref(x_18);
if (x_17 == 2)
{
uint8_t x_37; 
x_37 = 1;
x_34 = x_37;
goto block_36;
}
else
{
uint8_t x_38; 
x_38 = 0;
x_34 = x_38;
goto block_36;
}
block_36:
{
lean_object* x_35; 
lean_inc_ref(x_10);
x_35 = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild_spec__0(x_10, x_11, x_12, x_1, x_10, x_33, x_34);
goto block_32;
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_10);
lean_dec_ref(x_1);
goto block_32;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_io_user_error(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_32:
{
if (lean_obj_tag(x_14) == 0)
{
if (x_16 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec_ref(x_14);
x_6 = x_19;
goto block_9;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec_ref(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec_ref(x_14);
x_6 = x_21;
goto block_9;
}
else
{
uint8_t x_22; lean_object* x_23; 
lean_dec_ref(x_14);
x_22 = lean_uint8_once(&l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0, &l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0_once, _init_l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild___redArg___closed__0);
x_23 = lean_io_exit(x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_13);
x_24 = lean_ctor_get(x_14, 0);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
x_25 = x_14;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
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
x_6 = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_21; 
x_6 = lean_ctor_get(x_4, 0);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_7 = x_4;
x_8 = x_21;
goto block_20;
}
else
{
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_19; 
x_9 = lean_ctor_get(x_5, 0);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
x_10 = x_5;
x_11 = x_19;
goto block_18;
}
else
{
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_9);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_46; 
x_23 = lean_ctor_get(x_5, 0);
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
x_24 = x_5;
x_25 = x_46;
goto block_45;
}
else
{
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_43; 
x_26 = lean_ctor_get(x_4, 0);
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_4, 1);
lean_dec(x_44);
x_27 = x_4;
x_28 = x_43;
goto block_42;
}
else
{
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_box(0);
x_28 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_29);
lean_dec(x_23);
x_30 = lean_io_wait(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_31);
x_32 = x_24;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_31);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_32);
x_33 = x_27;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_30);
lean_del_object(x_24);
x_38 = ((lean_object*)(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1));
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_38);
x_39 = x_27;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
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
x_4 = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
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
x_5 = ((lean_object*)(l_Lake_mkBuildContext___closed__0));
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
res = runtime_initialize_Lake_Config_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Index(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
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
res = initialize_Lake_Config_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Run(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Run(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Run(builtin);
}
#ifdef __cplusplus
}
#endif
