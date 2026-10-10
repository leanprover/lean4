// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: public import Lake.Load.Config public import Lake.Build.Context public import Lake.Util.Exit import Lake.Build.Run import Lake.Build.Module import Lake.Load.Package import Lake.Load.Lean.Elab import Lake.Load.Workspace import Lake.Util.IO
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_get_stderr();
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* l_Lake_setupServerModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
extern lean_object* l_Lake_configModuleName;
lean_object* l_Lean_Plugin_ofFilePath(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
lean_object* l_Lake_Log_toString(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
static const lean_string_object l_Lake_invalidConfigEnvVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LAKE_INVALID_CONFIG"};
static const lean_object* l_Lake_invalidConfigEnvVar___closed__0 = (const lean_object*)&l_Lake_invalidConfigEnvVar___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_invalidConfigEnvVar = (const lean_object*)&l_Lake_invalidConfigEnvVar___closed__0_value;
static lean_once_cell_t l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.CLI.Serve"};
static const lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0 = (const lean_object*)&l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lake.CLI.Serve.0.Lake.setupFile.print!"};
static const lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1 = (const lean_object*)&l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to print `setup-file` result: "};
static const lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2 = (const lean_object*)&l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2_value;
LEAN_EXPORT uint32_t l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lake.CLI.Serve.0.Lake.setupFile.eprint!"};
static const lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0 = (const lean_object*)&l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Failed to print `setup-file` error: "};
static const lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1 = (const lean_object*)&l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "\nOriginal error:\n"};
static const lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2 = (const lean_object*)&l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "Failed to configure the Lake workspace. Please restart the server after fixing the error above.\n"};
static const lean_object* l_Lake_setupFile___closed__0 = (const lean_object*)&l_Lake_setupFile___closed__0_value;
static const lean_string_object l_Lake_setupFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to build module dependencies.\n"};
static const lean_object* l_Lake_setupFile___closed__1 = (const lean_object*)&l_Lake_setupFile___closed__1_value;
static const lean_string_object l_Lake_setupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Failed to load the Lake workspace.\n"};
static const lean_object* l_Lake_setupFile___closed__2 = (const lean_object*)&l_Lake_setupFile___closed__2_value;
static const lean_array_object l_Lake_setupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_setupFile___closed__3 = (const lean_object*)&l_Lake_setupFile___closed__3_value;
LEAN_EXPORT uint32_t l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_serve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_serve___closed__0 = (const lean_object*)&l_Lake_serve___closed__0_value;
static const lean_string_object l_Lake_serve___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--server"};
static const lean_object* l_Lake_serve___closed__1 = (const lean_object*)&l_Lake_serve___closed__1_value;
static const lean_array_object l_Lake_serve___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_serve___closed__1_value)}};
static const lean_object* l_Lake_serve___closed__2 = (const lean_object*)&l_Lake_serve___closed__2_value;
static const lean_string_object l_Lake_serve___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "warning: package configuration has errors, falling back to plain `lean --server`"};
static const lean_object* l_Lake_serve___closed__3 = (const lean_object*)&l_Lake_serve___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
static uint32_t _init_l_Lake_noConfigFileCode(void){
_start:
{
uint32_t v___x_1_; 
v___x_1_ = 2;
return v___x_1_;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = l_instMonadBaseIO;
v___x_6_ = l_instInhabitedOfMonad___redArg(v___x_5_, v___x_4_);
return v___x_6_;
}
}
lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(lean_object* v_msg_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_286__overap_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0);
v___x_286__overap_10_ = lean_panic_fn_borrowed(v___x_9_, v_msg_7_);
v___x_11_ = lean_apply_1(v___x_286__overap_10_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_7_ = stack[0].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v_msg_7_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___boxed(lean_object* v_msg_13_, lean_object* v___y_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v_msg_13_);
return v_res_15_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object* v_s_16_){
_start:
{
lean_object* v___x_18_; lean_object* v_putStr_19_; lean_object* v___x_20_; 
v___x_18_ = lean_get_stdout();
v_putStr_19_ = lean_ctor_get(v___x_18_, 4);
lean_inc_ref(v_putStr_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lean_apply_2(v_putStr_19_, v_s_16_, lean_box(0));
return v___x_20_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_16_ = stack[0].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v_s_16_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0___boxed(lean_object* v_s_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v_s_22_);
return v_res_24_;
}
}
lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object* v_s_25_){
_start:
{
uint32_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = 10;
v___x_28_ = lean_string_push(v_s_25_, v___x_27_);
v___x_29_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_25_ = stack[0].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(v_s_25_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0___boxed(lean_object* v_s_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(v_s_31_);
return v_res_33_;
}
}
uint32_t l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object* v_msg_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(v_msg_37_);
if (lean_obj_tag(v___x_39_) == 0)
{
uint32_t v___x_40_; 
lean_dec_ref_known(v___x_39_, 1);
v___x_40_ = 0;
return v___x_40_;
}
else
{
lean_object* v_a_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint32_t v___x_51_; 
v_a_41_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_41_);
lean_dec_ref_known(v___x_39_, 1);
v___x_42_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0));
v___x_43_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1));
v___x_44_ = lean_unsigned_to_nat(80u);
v___x_45_ = lean_unsigned_to_nat(6u);
v___x_46_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2));
v___x_47_ = lean_io_error_to_string(v_a_41_);
v___x_48_ = lean_string_append(v___x_46_, v___x_47_);
lean_dec_ref(v___x_47_);
v___x_49_ = l_mkPanicMessageWithDecl(v___x_42_, v___x_43_, v___x_44_, v___x_45_, v___x_48_);
lean_dec_ref(v___x_48_);
v___x_50_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v___x_49_);
v___x_51_ = 1;
return v___x_51_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_37_ = stack[0].m_obj;
uint32_t v_res_52_;
v_res_52_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v_msg_37_);
stack->m_num = v_res_52_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed(lean_object* v_msg_53_, lean_object* v_a_54_){
_start:
{
uint32_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v_msg_53_);
v_r_56_ = lean_box_uint32(v_res_55_);
return v_r_56_;
}
}
lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object* v_s_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_putStr_60_; lean_object* v___x_61_; 
v___x_59_ = lean_get_stderr();
v_putStr_60_ = lean_ctor_get(v___x_59_, 4);
lean_inc_ref(v_putStr_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = lean_apply_2(v_putStr_60_, v_s_57_, lean_box(0));
return v___x_61_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_57_ = stack[0].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v_s_57_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0___boxed(lean_object* v_s_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v_s_63_);
return v_res_65_;
}
}
lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object* v_msg_69_){
_start:
{
lean_object* v___x_71_; 
lean_inc_ref(v_msg_69_);
v___x_71_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v_msg_69_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; 
lean_dec_ref(v_msg_69_);
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_71_, 1);
return v_a_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_a_73_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_71_, 1);
v___x_74_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0));
v___x_75_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0));
v___x_76_ = lean_unsigned_to_nat(84u);
v___x_77_ = lean_unsigned_to_nat(6u);
v___x_78_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1));
v___x_79_ = lean_io_error_to_string(v_a_73_);
v___x_80_ = lean_string_append(v___x_78_, v___x_79_);
lean_dec_ref(v___x_79_);
v___x_81_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2));
v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
v___x_83_ = lean_string_append(v___x_82_, v_msg_69_);
lean_dec_ref(v_msg_69_);
v___x_84_ = l_mkPanicMessageWithDecl(v___x_74_, v___x_75_, v___x_76_, v___x_77_, v___x_83_);
lean_dec_ref(v___x_83_);
v___x_85_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_69_ = stack[0].m_obj;
lean_object* v_res_86_;
v_res_86_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_msg_69_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___boxed(lean_object* v_msg_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_msg_87_);
return v_res_89_;
}
}
lean_object* l_Lake_setupFile___lam__0(lean_object* v_val_90_, uint8_t v_outLv_91_, uint8_t v_val_92_, lean_object* v_e_93_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lake_logToStream(v_e_93_, v_val_90_, v_outLv_91_, v_val_92_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Lake_setupFile___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_90_ = stack[0].m_obj;
uint8_t v_outLv_91_ = stack[1].m_num;
uint8_t v_val_92_ = stack[2].m_num;
lean_object* v_e_93_ = stack[3].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lake_setupFile___lam__0(v_val_90_, v_outLv_91_, v_val_92_, v_e_93_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* v_val_97_, lean_object* v_outLv_98_, lean_object* v_val_99_, lean_object* v_e_100_, lean_object* v___y_101_){
_start:
{
uint8_t v_outLv_boxed_102_; uint8_t v_val_1034__boxed_103_; lean_object* v_res_104_; 
v_outLv_boxed_102_ = lean_unbox(v_outLv_98_);
v_val_1034__boxed_103_ = lean_unbox(v_val_99_);
v_res_104_ = l_Lake_setupFile___lam__0(v_val_97_, v_outLv_boxed_102_, v_val_1034__boxed_103_, v_e_100_);
lean_dec_ref(v_e_100_);
return v_res_104_;
}
}
uint32_t l_Lake_setupFile(lean_object* v_loadConfig_110_, lean_object* v_leanFile_111_, lean_object* v_header_x3f_112_, lean_object* v_buildConfig_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_lakeEnv_116_; lean_object* v_configFile_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
lean_inc_ref(v_leanFile_111_);
v___x_115_ = l_Lake_resolvePath(v_leanFile_111_);
v_lakeEnv_116_ = lean_ctor_get(v_loadConfig_110_, 0);
v_configFile_117_ = lean_ctor_get(v_loadConfig_110_, 8);
lean_inc_ref(v_configFile_117_);
v___x_118_ = l_Lake_realConfigFile(v_configFile_117_);
v___x_119_ = lean_string_utf8_byte_size(v___x_118_);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_nat_dec_eq(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = lean_string_dec_eq(v___x_118_, v___x_115_);
lean_dec_ref(v___x_118_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lake_invalidConfigEnvVar___closed__0));
v___x_124_ = lean_io_getenv(v___x_123_);
if (lean_obj_tag(v___x_124_) == 1)
{
lean_object* v_val_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint32_t v___x_129_; 
lean_dec_ref(v___x_115_);
lean_dec_ref(v_buildConfig_113_);
lean_dec(v_header_x3f_112_);
lean_dec_ref(v_leanFile_111_);
lean_dec_ref(v_loadConfig_110_);
v_val_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_val_125_);
v___x_127_ = ((lean_object*)(l_Lake_setupFile___closed__0));
v___x_128_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_127_);
v___x_129_ = 1;
return v___x_129_;
}
else
{
lean_object* v_toLogConfig_130_; uint8_t v_outLv_131_; uint8_t v_ansiMode_132_; lean_object* v_out_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
lean_dec(v___x_124_);
v_toLogConfig_130_ = lean_ctor_get(v_buildConfig_113_, 0);
v_outLv_131_ = lean_ctor_get_uint8(v_toLogConfig_130_, sizeof(void*)*1 + 1);
v_ansiMode_132_ = lean_ctor_get_uint8(v_toLogConfig_130_, sizeof(void*)*1 + 2);
v_out_133_ = lean_ctor_get(v_toLogConfig_130_, 0);
v___x_134_ = l_Lake_OutStream_get(v_out_133_);
lean_inc_ref(v___x_134_);
v___x_135_ = l_Lake_AnsiMode_isEnabled(v___x_134_, v_ansiMode_132_);
v___x_136_ = lean_box(v_outLv_131_);
v___x_137_ = lean_box(v___x_135_);
v___f_138_ = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(v___f_138_, 0, v___x_134_);
lean_closure_set(v___f_138_, 1, v___x_136_);
lean_closure_set(v___f_138_, 2, v___x_137_);
v___x_139_ = l_Lake_loadWorkspace(v_loadConfig_110_, v___f_138_);
lean_dec_ref(v___f_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_139_, 1);
v___x_141_ = lean_alloc_closure((void*)(l_Lake_setupServerModule___boxed), 10, 3);
lean_closure_set(v___x_141_, 0, v_leanFile_111_);
lean_closure_set(v___x_141_, 1, v___x_115_);
lean_closure_set(v___x_141_, 2, v_header_x3f_112_);
v___x_142_ = l_Lake_Workspace_runBuild___redArg(v_a_140_, v___x_141_, v_buildConfig_113_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint32_t v___x_146_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_142_, 1);
v___x_144_ = l_Lean_instToJsonModuleSetup_toJson(v_a_143_);
v___x_145_ = l_Lean_Json_compress(v___x_144_);
v___x_146_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v___x_145_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; uint32_t v___x_149_; 
lean_dec_ref_known(v___x_142_, 1);
v___x_147_ = ((lean_object*)(l_Lake_setupFile___closed__1));
v___x_148_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_147_);
v___x_149_ = 1;
return v___x_149_;
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; uint32_t v___x_152_; 
lean_dec_ref_known(v___x_139_, 1);
lean_dec_ref(v___x_115_);
lean_dec_ref(v_buildConfig_113_);
lean_dec(v_header_x3f_112_);
lean_dec_ref(v_leanFile_111_);
v___x_150_ = ((lean_object*)(l_Lake_setupFile___closed__2));
v___x_151_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_150_);
v___x_152_ = 1;
return v___x_152_;
}
}
}
else
{
lean_object* v_lake_153_; lean_object* v_sharedDynlib_154_; lean_object* v_path_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint32_t v___x_167_; 
lean_inc_ref(v_lakeEnv_116_);
lean_dec_ref(v___x_115_);
lean_dec_ref(v_buildConfig_113_);
lean_dec(v_header_x3f_112_);
lean_dec_ref(v_leanFile_111_);
lean_dec_ref(v_loadConfig_110_);
v_lake_153_ = lean_ctor_get(v_lakeEnv_116_, 0);
lean_inc_ref(v_lake_153_);
lean_dec_ref(v_lakeEnv_116_);
v_sharedDynlib_154_ = lean_ctor_get(v_lake_153_, 4);
lean_inc_ref(v_sharedDynlib_154_);
lean_dec_ref(v_lake_153_);
v_path_155_ = lean_ctor_get(v_sharedDynlib_154_, 0);
lean_inc_ref(v_path_155_);
lean_dec_ref(v_sharedDynlib_154_);
v___x_156_ = l_Lake_configModuleName;
v___x_157_ = lean_box(0);
v___x_158_ = lean_box(1);
v___x_159_ = ((lean_object*)(l_Lake_setupFile___closed__3));
v___x_160_ = l_Lean_Plugin_ofFilePath(v_path_155_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_array_push(v___x_162_, v___x_160_);
v___x_164_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_164_, 0, v___x_156_);
lean_ctor_set(v___x_164_, 1, v___x_157_);
lean_ctor_set(v___x_164_, 2, v___x_157_);
lean_ctor_set(v___x_164_, 3, v___x_158_);
lean_ctor_set(v___x_164_, 4, v___x_159_);
lean_ctor_set(v___x_164_, 5, v___x_163_);
lean_ctor_set(v___x_164_, 6, v___x_158_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*7, v___x_121_);
v___x_165_ = l_Lean_instToJsonModuleSetup_toJson(v___x_164_);
v___x_166_ = l_Lean_Json_compress(v___x_165_);
v___x_167_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v___x_166_);
return v___x_167_;
}
}
else
{
uint32_t v___x_168_; 
lean_dec_ref(v___x_118_);
lean_dec_ref(v___x_115_);
lean_dec_ref(v_buildConfig_113_);
lean_dec(v_header_x3f_112_);
lean_dec_ref(v_leanFile_111_);
lean_dec_ref(v_loadConfig_110_);
v___x_168_ = 2;
return v___x_168_;
}
}
}
LEAN_EXPORT void l_Lake_setupFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_loadConfig_110_ = stack[0].m_obj;
lean_object* v_leanFile_111_ = stack[1].m_obj;
lean_object* v_header_x3f_112_ = stack[2].m_obj;
lean_object* v_buildConfig_113_ = stack[3].m_obj;
uint32_t v_res_169_;
v_res_169_ = l_Lake_setupFile(v_loadConfig_110_, v_leanFile_111_, v_header_x3f_112_, v_buildConfig_113_);
stack->m_num = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object* v_loadConfig_170_, lean_object* v_leanFile_171_, lean_object* v_header_x3f_172_, lean_object* v_buildConfig_173_, lean_object* v_a_174_){
_start:
{
uint32_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lake_setupFile(v_loadConfig_170_, v_leanFile_171_, v_header_x3f_172_, v_buildConfig_173_);
v_r_176_ = lean_box_uint32(v_res_175_);
return v_r_176_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(lean_object* v_as_177_, size_t v_i_178_, size_t v_stop_179_, lean_object* v_b_180_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_eq(v_i_178_, v_stop_179_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; uint8_t v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; 
v___x_183_ = lean_box(1);
v___x_184_ = 1;
v___x_185_ = 0;
v___x_186_ = lean_array_uget_borrowed(v_as_177_, v_i_178_);
v___x_187_ = l_Lake_OutStream_logEntry(v___x_183_, v___x_186_, v___x_184_, v___x_185_);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_178_, v___x_188_);
v_i_178_ = v___x_189_;
v_b_180_ = v___x_187_;
goto _start;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v_b_180_);
return v___x_191_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_177_ = stack[0].m_obj;
size_t v_i_178_ = stack[1].m_num;
size_t v_stop_179_ = stack[2].m_num;
lean_object* v_b_180_ = stack[3].m_obj;
lean_object* v_res_192_;
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_as_177_, v_i_178_, v_stop_179_, v_b_180_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1___boxed(lean_object* v_as_193_, lean_object* v_i_194_, lean_object* v_stop_195_, lean_object* v_b_196_, lean_object* v___y_197_){
_start:
{
size_t v_i_boxed_198_; size_t v_stop_boxed_199_; lean_object* v_res_200_; 
v_i_boxed_198_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_stop_boxed_199_ = lean_unbox_usize(v_stop_195_);
lean_dec(v_stop_195_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_as_193_, v_i_boxed_198_, v_stop_boxed_199_, v_b_196_);
lean_dec_ref(v_as_193_);
return v_res_200_;
}
}
lean_object* l_IO_eprintln___at___00Lake_serve_spec__0(lean_object* v_s_201_){
_start:
{
uint32_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = 10;
v___x_204_ = lean_string_push(v_s_201_, v___x_203_);
v___x_205_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00Lake_serve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_201_ = stack[0].m_obj;
lean_object* v_res_206_;
v_res_206_ = l_IO_eprintln___at___00Lake_serve_spec__0(v_s_201_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0___boxed(lean_object* v_s_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_IO_eprintln___at___00Lake_serve_spec__0(v_s_207_);
return v_res_209_;
}
}
lean_object* l_Lake_serve(lean_object* v_config_218_, lean_object* v_args_219_){
_start:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_296_; 
lean_inc_ref(v_config_218_);
v___x_246_ = lean_alloc_closure((void*)(l_Lake_loadWorkspace___boxed), 3, 1);
lean_closure_set(v___x_246_, 0, v_config_218_);
v___x_247_ = l_Lake_LoggerIO_captureLog___redArg(v___x_246_);
v_fst_248_ = lean_ctor_get(v___x_247_, 0);
v_snd_249_ = lean_ctor_get(v___x_247_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_296_ == 0)
{
v___x_251_ = v___x_247_;
v_isShared_252_ = v_isSharedCheck_296_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snd_249_);
lean_inc(v_fst_248_);
lean_dec(v___x_247_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_296_;
goto v_resetjp_250_;
}
v___jp_221_:
{
lean_object* v___x_224_; lean_object* v_lakeEnv_225_; lean_object* v_lean_226_; lean_object* v_lean_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_224_ = ((lean_object*)(l_Lake_serve___closed__0));
v_lakeEnv_225_ = lean_ctor_get(v_config_218_, 0);
lean_inc_ref(v_lakeEnv_225_);
lean_dec_ref(v_config_218_);
v_lean_226_ = lean_ctor_get(v_lakeEnv_225_, 1);
lean_inc_ref(v_lean_226_);
lean_dec_ref(v_lakeEnv_225_);
v_lean_227_ = lean_ctor_get(v_lean_226_, 7);
lean_inc_ref(v_lean_227_);
lean_dec_ref(v_lean_226_);
v___x_228_ = ((lean_object*)(l_Lake_serve___closed__2));
v___x_229_ = l_Array_append___redArg(v___x_228_, v_snd_223_);
lean_dec_ref(v_snd_223_);
v___x_230_ = l_Array_append___redArg(v___x_229_, v_args_219_);
v___x_231_ = lean_box(0);
v___x_232_ = 1;
v___x_233_ = 0;
v___x_234_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_234_, 0, v___x_224_);
lean_ctor_set(v___x_234_, 1, v_lean_227_);
lean_ctor_set(v___x_234_, 2, v___x_230_);
lean_ctor_set(v___x_234_, 3, v___x_231_);
lean_ctor_set(v___x_234_, 4, v_fst_222_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*5, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*5 + 1, v___x_233_);
v___x_235_ = lean_io_process_spawn(v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = lean_io_process_child_wait(v___x_224_, v_a_236_);
lean_dec(v_a_236_);
return v___x_237_;
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_235_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_235_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
v_resetjp_250_:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_array_get_size(v_snd_249_);
v___x_283_ = lean_nat_dec_lt(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
goto v___jp_253_;
}
else
{
lean_object* v___x_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v___x_284_ = lean_box(0);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = lean_usize_of_nat(v___x_282_);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_snd_249_, v___x_285_, v___x_286_, v___x_284_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_dec_ref_known(v___x_287_, 1);
goto v___jp_253_;
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_del_object(v___x_251_);
lean_dec(v_snd_249_);
lean_dec(v_fst_248_);
lean_dec_ref(v_config_218_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
v___jp_253_:
{
if (lean_obj_tag(v_fst_248_) == 1)
{
lean_object* v_val_254_; lean_object* v_packages_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_config_258_; lean_object* v_moreGlobalServerArgs_259_; lean_object* v___x_260_; 
lean_del_object(v___x_251_);
lean_dec(v_snd_249_);
v_val_254_ = lean_ctor_get(v_fst_248_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v_fst_248_, 1);
v_packages_255_ = lean_ctor_get(v_val_254_, 4);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_array_fget_borrowed(v_packages_255_, v___x_256_);
v_config_258_ = lean_ctor_get(v___x_257_, 6);
v_moreGlobalServerArgs_259_ = lean_ctor_get(v_config_258_, 3);
lean_inc_ref(v_moreGlobalServerArgs_259_);
v___x_260_ = l_Lake_Workspace_augmentedEnvVars(v_val_254_);
v_fst_222_ = v___x_260_;
v_snd_223_ = v_moreGlobalServerArgs_259_;
goto v___jp_221_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_fst_248_);
v___x_261_ = ((lean_object*)(l_Lake_serve___closed__3));
v___x_262_ = l_IO_eprintln___at___00Lake_serve_spec__0(v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_lakeEnv_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec_ref_known(v___x_262_, 1);
v_lakeEnv_263_ = lean_ctor_get(v_config_218_, 0);
lean_inc_ref(v_lakeEnv_263_);
v___x_264_ = l_Lake_Env_baseVars(v_lakeEnv_263_);
v___x_265_ = ((lean_object*)(l_Lake_invalidConfigEnvVar___closed__0));
v___x_266_ = l_Lake_Log_toString(v_snd_249_);
lean_dec(v_snd_249_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_267_);
lean_ctor_set(v___x_251_, 0, v___x_265_);
v___x_269_ = v___x_251_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_267_);
v___x_269_ = v_reuseFailAlloc_272_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_array_push(v___x_264_, v___x_269_);
v___x_271_ = ((lean_object*)(l_Lake_setupFile___closed__3));
v_fst_222_ = v___x_270_;
v_snd_223_ = v___x_271_;
goto v___jp_221_;
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_del_object(v___x_251_);
lean_dec(v_snd_249_);
lean_dec_ref(v_config_218_);
v_a_273_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_262_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_262_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_serve_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_218_ = stack[0].m_obj;
lean_object* v_args_219_ = stack[1].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lake_serve(v_config_218_, v_args_219_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* v_config_298_, lean_object* v_args_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lake_serve(v_config_298_, v_args_299_);
lean_dec_ref(v_args_299_);
return v_res_301_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Context(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Run(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Module(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Elab(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Serve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Serve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Build_Context(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* initialize_Lake_Build_Run(uint8_t builtin);
lean_object* initialize_Lake_Build_Module(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Serve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Serve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Serve(builtin);
}
#ifdef __cplusplus
}
#endif
