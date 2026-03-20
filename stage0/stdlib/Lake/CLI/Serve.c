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
lean_object* l_instMonadST(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
lean_object* l_Lake_Log_toString(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v___x_4_; 
v___x_4_ = l_instMonadST(lean_box(0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(lean_object* v_msg_5_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_449__overap_10_; lean_object* v___x_11_; 
v___x_7_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0);
v___x_8_ = lean_box(0);
v___x_9_ = l_instInhabitedOfMonad___redArg(v___x_7_, v___x_8_);
v___x_449__overap_10_ = lean_panic_fn(v___x_9_, v_msg_5_);
v___x_11_ = lean_apply_1(v___x_449__overap_10_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___boxed(lean_object* v_msg_12_, lean_object* v___y_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v_msg_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object* v_s_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_putStr_18_; lean_object* v___x_19_; 
v___x_17_ = lean_get_stdout();
v_putStr_18_ = lean_ctor_get(v___x_17_, 4);
lean_inc_ref(v_putStr_18_);
lean_dec_ref(v___x_17_);
v___x_19_ = lean_apply_2(v_putStr_18_, v_s_15_, lean_box(0));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0___boxed(lean_object* v_s_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v_s_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object* v_s_23_){
_start:
{
uint32_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = 10;
v___x_26_ = lean_string_push(v_s_23_, v___x_25_);
v___x_27_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0___boxed(lean_object* v_s_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(v_s_28_);
return v_res_30_;
}
}
LEAN_EXPORT uint32_t l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object* v_msg_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(v_msg_34_);
if (lean_obj_tag(v___x_36_) == 0)
{
uint32_t v___x_37_; 
lean_dec_ref(v___x_36_);
v___x_37_ = 0;
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint32_t v___x_48_; 
v_a_38_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_38_);
lean_dec_ref(v___x_36_);
v___x_39_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0));
v___x_40_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1));
v___x_41_ = lean_unsigned_to_nat(80u);
v___x_42_ = lean_unsigned_to_nat(6u);
v___x_43_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2));
v___x_44_ = lean_io_error_to_string(v_a_38_);
v___x_45_ = lean_string_append(v___x_43_, v___x_44_);
lean_dec_ref(v___x_44_);
v___x_46_ = l_mkPanicMessageWithDecl(v___x_39_, v___x_40_, v___x_41_, v___x_42_, v___x_45_);
lean_dec_ref(v___x_45_);
v___x_47_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v___x_46_);
v___x_48_ = 1;
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed(lean_object* v_msg_49_, lean_object* v_a_50_){
_start:
{
uint32_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v_msg_49_);
v_r_52_ = lean_box_uint32(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object* v_s_53_){
_start:
{
lean_object* v___x_55_; lean_object* v_putStr_56_; lean_object* v___x_57_; 
v___x_55_ = lean_get_stderr();
v_putStr_56_ = lean_ctor_get(v___x_55_, 4);
lean_inc_ref(v_putStr_56_);
lean_dec_ref(v___x_55_);
v___x_57_ = lean_apply_2(v_putStr_56_, v_s_53_, lean_box(0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0___boxed(lean_object* v_s_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v_s_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object* v_msg_64_){
_start:
{
lean_object* v___x_66_; 
lean_inc_ref(v_msg_64_);
v___x_66_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v_msg_64_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; 
lean_dec_ref(v_msg_64_);
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v___x_66_);
return v_a_67_;
}
else
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_a_68_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v___x_66_);
v___x_69_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0));
v___x_70_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0));
v___x_71_ = lean_unsigned_to_nat(84u);
v___x_72_ = lean_unsigned_to_nat(6u);
v___x_73_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1));
v___x_74_ = lean_io_error_to_string(v_a_68_);
v___x_75_ = lean_string_append(v___x_73_, v___x_74_);
lean_dec_ref(v___x_74_);
v___x_76_ = ((lean_object*)(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2));
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
v___x_78_ = lean_string_append(v___x_77_, v_msg_64_);
lean_dec_ref(v_msg_64_);
v___x_79_ = l_mkPanicMessageWithDecl(v___x_69_, v___x_70_, v___x_71_, v___x_72_, v___x_78_);
lean_dec_ref(v___x_78_);
v___x_80_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v___x_79_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___boxed(lean_object* v_msg_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_msg_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object* v_val_84_, uint8_t v_outLv_85_, uint8_t v_val_86_, lean_object* v_e_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lake_logToStream(v_e_87_, v_val_84_, v_outLv_85_, v_val_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* v_val_90_, lean_object* v_outLv_91_, lean_object* v_val_92_, lean_object* v_e_93_, lean_object* v___y_94_){
_start:
{
uint8_t v_outLv_boxed_95_; uint8_t v_val_1784__boxed_96_; lean_object* v_res_97_; 
v_outLv_boxed_95_ = lean_unbox(v_outLv_91_);
v_val_1784__boxed_96_ = lean_unbox(v_val_92_);
v_res_97_ = l_Lake_setupFile___lam__0(v_val_90_, v_outLv_boxed_95_, v_val_1784__boxed_96_, v_e_93_);
lean_dec_ref(v_e_93_);
return v_res_97_;
}
}
LEAN_EXPORT uint32_t l_Lake_setupFile(lean_object* v_loadConfig_103_, lean_object* v_leanFile_104_, lean_object* v_header_x3f_105_, lean_object* v_buildConfig_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_lakeEnv_109_; lean_object* v_configFile_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
lean_inc_ref(v_leanFile_104_);
v___x_108_ = l_Lake_resolvePath(v_leanFile_104_);
v_lakeEnv_109_ = lean_ctor_get(v_loadConfig_103_, 0);
v_configFile_110_ = lean_ctor_get(v_loadConfig_103_, 8);
lean_inc_ref(v_configFile_110_);
v___x_111_ = l_Lake_realConfigFile(v_configFile_110_);
v___x_112_ = lean_string_utf8_byte_size(v___x_111_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = lean_string_dec_eq(v___x_111_, v___x_108_);
lean_dec_ref(v___x_111_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lake_invalidConfigEnvVar___closed__0));
v___x_117_ = lean_io_getenv(v___x_116_);
if (lean_obj_tag(v___x_117_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint32_t v___x_122_; 
lean_dec_ref(v___x_108_);
lean_dec_ref(v_buildConfig_106_);
lean_dec(v_header_x3f_105_);
lean_dec_ref(v_leanFile_104_);
lean_dec_ref(v_loadConfig_103_);
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref(v___x_117_);
v___x_119_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_val_118_);
v___x_120_ = ((lean_object*)(l_Lake_setupFile___closed__0));
v___x_121_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_120_);
v___x_122_ = 1;
return v___x_122_;
}
else
{
lean_object* v_toLogConfig_123_; uint8_t v_outLv_124_; uint8_t v_ansiMode_125_; lean_object* v_out_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
lean_dec(v___x_117_);
v_toLogConfig_123_ = lean_ctor_get(v_buildConfig_106_, 0);
v_outLv_124_ = lean_ctor_get_uint8(v_toLogConfig_123_, sizeof(void*)*1 + 1);
v_ansiMode_125_ = lean_ctor_get_uint8(v_toLogConfig_123_, sizeof(void*)*1 + 2);
v_out_126_ = lean_ctor_get(v_toLogConfig_123_, 0);
v___x_127_ = l_Lake_OutStream_get(v_out_126_);
lean_inc_ref(v___x_127_);
v___x_128_ = l_Lake_AnsiMode_isEnabled(v___x_127_, v_ansiMode_125_);
v___x_129_ = lean_box(v_outLv_124_);
v___x_130_ = lean_box(v___x_128_);
v___f_131_ = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(v___f_131_, 0, v___x_127_);
lean_closure_set(v___f_131_, 1, v___x_129_);
lean_closure_set(v___f_131_, 2, v___x_130_);
v___x_132_ = l_Lake_loadWorkspace(v_loadConfig_103_, v___f_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref(v___x_132_);
v___x_134_ = lean_alloc_closure((void*)(l_Lake_setupServerModule___boxed), 10, 3);
lean_closure_set(v___x_134_, 0, v_leanFile_104_);
lean_closure_set(v___x_134_, 1, v___x_108_);
lean_closure_set(v___x_134_, 2, v_header_x3f_105_);
v___x_135_ = l_Lake_Workspace_runBuild___redArg(v_a_133_, v___x_134_, v_buildConfig_106_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint32_t v___x_139_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref(v___x_135_);
v___x_137_ = l_Lean_instToJsonModuleSetup_toJson(v_a_136_);
v___x_138_ = l_Lean_Json_compress(v___x_137_);
v___x_139_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v___x_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; uint32_t v___x_142_; 
lean_dec_ref(v___x_135_);
v___x_140_ = ((lean_object*)(l_Lake_setupFile___closed__1));
v___x_141_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_140_);
v___x_142_ = 1;
return v___x_142_;
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; uint32_t v___x_145_; 
lean_dec_ref(v___x_132_);
lean_dec_ref(v___x_108_);
lean_dec_ref(v_buildConfig_106_);
lean_dec(v_header_x3f_105_);
lean_dec_ref(v_leanFile_104_);
v___x_143_ = ((lean_object*)(l_Lake_setupFile___closed__2));
v___x_144_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_143_);
v___x_145_ = 1;
return v___x_145_;
}
}
}
else
{
lean_object* v_lake_146_; lean_object* v_sharedDynlib_147_; lean_object* v_path_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint32_t v___x_159_; 
lean_inc_ref(v_lakeEnv_109_);
lean_dec_ref(v___x_108_);
lean_dec_ref(v_buildConfig_106_);
lean_dec(v_header_x3f_105_);
lean_dec_ref(v_leanFile_104_);
lean_dec_ref(v_loadConfig_103_);
v_lake_146_ = lean_ctor_get(v_lakeEnv_109_, 0);
lean_inc_ref(v_lake_146_);
lean_dec_ref(v_lakeEnv_109_);
v_sharedDynlib_147_ = lean_ctor_get(v_lake_146_, 4);
lean_inc_ref(v_sharedDynlib_147_);
lean_dec_ref(v_lake_146_);
v_path_148_ = lean_ctor_get(v_sharedDynlib_147_, 0);
lean_inc_ref(v_path_148_);
lean_dec_ref(v_sharedDynlib_147_);
v___x_149_ = l_Lake_configModuleName;
v___x_150_ = lean_box(0);
v___x_151_ = lean_box(1);
v___x_152_ = ((lean_object*)(l_Lake_setupFile___closed__3));
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
v___x_155_ = lean_array_push(v___x_154_, v_path_148_);
v___x_156_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_156_, 0, v___x_149_);
lean_ctor_set(v___x_156_, 1, v___x_150_);
lean_ctor_set(v___x_156_, 2, v___x_150_);
lean_ctor_set(v___x_156_, 3, v___x_151_);
lean_ctor_set(v___x_156_, 4, v___x_152_);
lean_ctor_set(v___x_156_, 5, v___x_155_);
lean_ctor_set(v___x_156_, 6, v___x_151_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7, v___x_114_);
v___x_157_ = l_Lean_instToJsonModuleSetup_toJson(v___x_156_);
v___x_158_ = l_Lean_Json_compress(v___x_157_);
v___x_159_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v___x_158_);
return v___x_159_;
}
}
else
{
uint32_t v___x_160_; 
lean_dec_ref(v___x_111_);
lean_dec_ref(v___x_108_);
lean_dec_ref(v_buildConfig_106_);
lean_dec(v_header_x3f_105_);
lean_dec_ref(v_leanFile_104_);
lean_dec_ref(v_loadConfig_103_);
v___x_160_ = 2;
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object* v_loadConfig_161_, lean_object* v_leanFile_162_, lean_object* v_header_x3f_163_, lean_object* v_buildConfig_164_, lean_object* v_a_165_){
_start:
{
uint32_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lake_setupFile(v_loadConfig_161_, v_leanFile_162_, v_header_x3f_163_, v_buildConfig_164_);
v_r_167_ = lean_box_uint32(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(lean_object* v_as_168_, size_t v_i_169_, size_t v_stop_170_, lean_object* v_b_171_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = lean_usize_dec_eq(v_i_169_, v_stop_170_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; size_t v___x_179_; size_t v___x_180_; 
v___x_174_ = lean_box(1);
v___x_175_ = 1;
v___x_176_ = 0;
v___x_177_ = lean_array_uget_borrowed(v_as_168_, v_i_169_);
v___x_178_ = l_Lake_OutStream_logEntry(v___x_174_, v___x_177_, v___x_175_, v___x_176_);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_add(v_i_169_, v___x_179_);
v_i_169_ = v___x_180_;
v_b_171_ = v___x_178_;
goto _start;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_b_171_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1___boxed(lean_object* v_as_183_, lean_object* v_i_184_, lean_object* v_stop_185_, lean_object* v_b_186_, lean_object* v___y_187_){
_start:
{
size_t v_i_boxed_188_; size_t v_stop_boxed_189_; lean_object* v_res_190_; 
v_i_boxed_188_ = lean_unbox_usize(v_i_184_);
lean_dec(v_i_184_);
v_stop_boxed_189_ = lean_unbox_usize(v_stop_185_);
lean_dec(v_stop_185_);
v_res_190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_as_183_, v_i_boxed_188_, v_stop_boxed_189_, v_b_186_);
lean_dec_ref(v_as_183_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0(lean_object* v_s_191_){
_start:
{
uint32_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = 10;
v___x_194_ = lean_string_push(v_s_191_, v___x_193_);
v___x_195_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0___boxed(lean_object* v_s_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_IO_eprintln___at___00Lake_serve_spec__0(v_s_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_serve(lean_object* v_config_207_, lean_object* v_args_208_){
_start:
{
lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_289_; 
lean_inc_ref(v_config_207_);
v___x_235_ = lean_alloc_closure((void*)(l_Lake_loadWorkspace___boxed), 3, 1);
lean_closure_set(v___x_235_, 0, v_config_207_);
v___x_236_ = l_Lake_LoggerIO_captureLog___redArg(v___x_235_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
v_snd_238_ = lean_ctor_get(v___x_236_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_289_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_289_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snd_238_);
lean_inc(v_fst_237_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_289_;
goto v_resetjp_239_;
}
v___jp_210_:
{
lean_object* v___x_213_; lean_object* v_lakeEnv_214_; lean_object* v_lean_215_; lean_object* v_lean_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_213_ = ((lean_object*)(l_Lake_serve___closed__0));
v_lakeEnv_214_ = lean_ctor_get(v_config_207_, 0);
lean_inc_ref(v_lakeEnv_214_);
lean_dec_ref(v_config_207_);
v_lean_215_ = lean_ctor_get(v_lakeEnv_214_, 1);
lean_inc_ref(v_lean_215_);
lean_dec_ref(v_lakeEnv_214_);
v_lean_216_ = lean_ctor_get(v_lean_215_, 7);
lean_inc_ref(v_lean_216_);
lean_dec_ref(v_lean_215_);
v___x_217_ = ((lean_object*)(l_Lake_serve___closed__2));
v___x_218_ = l_Array_append___redArg(v___x_217_, v_snd_212_);
lean_dec_ref(v_snd_212_);
v___x_219_ = l_Array_append___redArg(v___x_218_, v_args_208_);
v___x_220_ = lean_box(0);
v___x_221_ = 1;
v___x_222_ = 0;
v___x_223_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_223_, 0, v___x_213_);
lean_ctor_set(v___x_223_, 1, v_lean_216_);
lean_ctor_set(v___x_223_, 2, v___x_219_);
lean_ctor_set(v___x_223_, 3, v___x_220_);
lean_ctor_set(v___x_223_, 4, v_fst_211_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*5, v___x_221_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*5 + 1, v___x_222_);
v___x_224_ = lean_io_process_spawn(v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v___x_224_);
v___x_226_ = lean_io_process_child_wait(v___x_213_, v_a_225_);
lean_dec(v_a_225_);
return v___x_226_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_227_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_224_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
v_resetjp_239_:
{
lean_object* v___y_269_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_array_get_size(v_snd_238_);
v___x_280_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
goto v___jp_242_;
}
else
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_box(0);
v___x_282_ = lean_nat_dec_le(v___x_279_, v___x_279_);
if (v___x_282_ == 0)
{
if (v___x_280_ == 0)
{
goto v___jp_242_;
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = ((size_t)0ULL);
v___x_284_ = lean_usize_of_nat(v___x_279_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_snd_238_, v___x_283_, v___x_284_, v___x_281_);
v___y_269_ = v___x_285_;
goto v___jp_268_;
}
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_279_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_snd_238_, v___x_286_, v___x_287_, v___x_281_);
v___y_269_ = v___x_288_;
goto v___jp_268_;
}
}
v___jp_242_:
{
if (lean_obj_tag(v_fst_237_) == 1)
{
lean_object* v_val_243_; lean_object* v_root_244_; lean_object* v_config_245_; lean_object* v_moreGlobalServerArgs_246_; lean_object* v___x_247_; 
lean_del_object(v___x_240_);
lean_dec(v_snd_238_);
v_val_243_ = lean_ctor_get(v_fst_237_, 0);
lean_inc(v_val_243_);
lean_dec_ref(v_fst_237_);
v_root_244_ = lean_ctor_get(v_val_243_, 0);
v_config_245_ = lean_ctor_get(v_root_244_, 6);
v_moreGlobalServerArgs_246_ = lean_ctor_get(v_config_245_, 3);
lean_inc_ref(v_moreGlobalServerArgs_246_);
v___x_247_ = l_Lake_Workspace_augmentedEnvVars(v_val_243_);
v_fst_211_ = v___x_247_;
v_snd_212_ = v_moreGlobalServerArgs_246_;
goto v___jp_210_;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_fst_237_);
v___x_248_ = ((lean_object*)(l_Lake_serve___closed__3));
v___x_249_ = l_IO_eprintln___at___00Lake_serve_spec__0(v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_lakeEnv_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
lean_dec_ref(v___x_249_);
v_lakeEnv_250_ = lean_ctor_get(v_config_207_, 0);
lean_inc_ref(v_lakeEnv_250_);
v___x_251_ = l_Lake_Env_baseVars(v_lakeEnv_250_);
v___x_252_ = ((lean_object*)(l_Lake_invalidConfigEnvVar___closed__0));
v___x_253_ = l_Lake_Log_toString(v_snd_238_);
lean_dec(v_snd_238_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_254_);
lean_ctor_set(v___x_240_, 0, v___x_252_);
v___x_256_ = v___x_240_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_254_);
v___x_256_ = v_reuseFailAlloc_259_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_array_push(v___x_251_, v___x_256_);
v___x_258_ = ((lean_object*)(l_Lake_setupFile___closed__3));
v_fst_211_ = v___x_257_;
v_snd_212_ = v___x_258_;
goto v___jp_210_;
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_del_object(v___x_240_);
lean_dec(v_snd_238_);
lean_dec_ref(v_config_207_);
v_a_260_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_249_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_249_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
v___jp_268_:
{
if (lean_obj_tag(v___y_269_) == 0)
{
lean_dec_ref(v___y_269_);
goto v___jp_242_;
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_del_object(v___x_240_);
lean_dec(v_snd_238_);
lean_dec(v_fst_237_);
lean_dec_ref(v_config_207_);
v_a_270_ = lean_ctor_get(v___y_269_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___y_269_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___y_269_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___y_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* v_config_290_, lean_object* v_args_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lake_serve(v_config_290_, v_args_291_);
lean_dec_ref(v_args_291_);
return v_res_293_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Serve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
