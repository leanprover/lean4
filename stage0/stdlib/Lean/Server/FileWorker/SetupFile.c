// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: public import Lean.Server.Utils public import Lean.Util.LakePath public import Lean.Server.ServerTask
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
lean_object* lean_io_prim_handle_get_line(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_Lean_determineLakePath();
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_load_dynlib(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value;
static const lean_array_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value;
static const lean_ctor_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "setup-file"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value;
static lean_once_cell_t l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--no-build"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value;
static const lean_string_object l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--no-cache"};
static const lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Invalid output from `"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_setupFile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed:\n"};
static const lean_object* l_Lean_Server_FileWorker_setupFile___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_setupFile___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* v_handleStderr_2_, lean_object* v_lakeProc_3_, lean_object* v_acc_4_){
_start:
{
lean_object* v_stderr_6_; lean_object* v___x_7_; 
v_stderr_6_ = lean_ctor_get(v_lakeProc_3_, 2);
v___x_7_ = lean_io_prim_handle_get_line(v_stderr_6_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_28_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_28_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_28_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_28_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_12_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
v___x_13_ = lean_string_dec_eq(v_a_8_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_del_object(v___x_10_);
lean_inc_ref(v_handleStderr_2_);
lean_inc(v_a_8_);
v___x_14_ = lean_apply_2(v_handleStderr_2_, v_a_8_, lean_box(0));
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v___x_15_; 
lean_dec_ref_known(v___x_14_, 1);
v___x_15_ = lean_string_append(v_acc_4_, v_a_8_);
lean_dec(v_a_8_);
v_acc_4_ = v___x_15_;
goto _start;
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
lean_dec(v_a_8_);
lean_dec_ref(v_acc_4_);
lean_dec_ref(v_handleStderr_2_);
v_a_17_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_14_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_14_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
lean_object* v___x_26_; 
lean_dec(v_a_8_);
lean_dec_ref(v_handleStderr_2_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v_acc_4_);
v___x_26_ = v___x_10_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_acc_4_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_dec_ref(v_acc_4_);
lean_dec_ref(v_handleStderr_2_);
return v___x_7_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_handleStderr_2_ = stack[0].m_obj;
lean_object* v_lakeProc_3_ = stack[1].m_obj;
lean_object* v_acc_4_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_2_, v_lakeProc_3_, v_acc_4_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* v_handleStderr_30_, lean_object* v_lakeProc_31_, lean_object* v_acc_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_30_, v_lakeProc_31_, v_acc_32_);
lean_dec_ref(v_lakeProc_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* v_lakePath_35_, lean_object* v_handleStderr_36_, lean_object* v_args_37_, lean_object* v_lakeProc_38_, lean_object* v_acc_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_36_, v_lakeProc_38_, v_acc_39_);
return v___x_41_;
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr_0interp(lean_interpreter_value* stack)
{
lean_object* v_lakePath_35_ = stack[0].m_obj;
lean_object* v_handleStderr_36_ = stack[1].m_obj;
lean_object* v_args_37_ = stack[2].m_obj;
lean_object* v_lakeProc_38_ = stack[3].m_obj;
lean_object* v_acc_39_ = stack[4].m_obj;
lean_object* v_res_42_;
v_res_42_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(v_lakePath_35_, v_handleStderr_36_, v_args_37_, v_lakeProc_38_, v_acc_39_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* v_lakePath_43_, lean_object* v_handleStderr_44_, lean_object* v_args_45_, lean_object* v_lakeProc_46_, lean_object* v_acc_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(v_lakePath_43_, v_handleStderr_44_, v_args_45_, v_lakeProc_46_, v_acc_47_);
lean_dec_ref(v_lakeProc_46_);
lean_dec_ref(v_args_45_);
lean_dec_ref(v_lakePath_43_);
return v_res_49_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object* v_e_50_){
_start:
{
if (lean_obj_tag(v_e_50_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_61_; 
v_a_52_ = lean_ctor_get(v_e_50_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_e_50_);
if (v_isSharedCheck_61_ == 0)
{
v___x_54_ = v_e_50_;
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v_e_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_56_ = lean_io_error_to_string(v_a_52_);
v___x_57_ = lean_mk_io_user_error(v___x_56_);
if (v_isShared_55_ == 0)
{
lean_ctor_set_tag(v___x_54_, 1);
lean_ctor_set(v___x_54_, 0, v___x_57_);
v___x_59_ = v___x_54_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v_e_50_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_e_50_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v_e_50_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v_e_50_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 0);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_50_ = stack[0].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_50_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object* v_e_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_71_);
return v_res_73_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object* v_00_u03b1_74_, lean_object* v_e_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_75_);
return v___x_77_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_75_ = stack[1].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_box(0), v_e_75_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object* v_00_u03b1_79_, lean_object* v_e_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(v_00_u03b1_79_, v_e_80_);
return v_res_82_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3));
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = lean_array_push(v___x_94_, v___x_92_);
return v___x_95_;
}
}
lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* v_m_98_, lean_object* v_lakePath_99_, lean_object* v_filePath_100_, lean_object* v_header_101_, lean_object* v_handleStderr_102_){
_start:
{
lean_object* v_args_105_; uint8_t v_dependencyBuildMode_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_args_202_; 
v_dependencyBuildMode_198_ = lean_ctor_get_uint8(v_m_98_, sizeof(void*)*4);
v___x_199_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4));
v___x_200_ = lean_obj_once(&l_Lean_Server_FileWorker_runLakeSetupFile___closed__5, &l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once, _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
v___x_201_ = lean_array_push(v___x_200_, v_filePath_100_);
v_args_202_ = lean_array_push(v___x_201_, v___x_199_);
if (v_dependencyBuildMode_198_ == 2)
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_args_206_; 
v___x_203_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6));
v___x_204_ = lean_array_push(v_args_202_, v___x_203_);
v___x_205_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7));
v_args_206_ = lean_array_push(v___x_204_, v___x_205_);
v_args_105_ = v_args_206_;
goto v___jp_104_;
}
else
{
v_args_105_ = v_args_202_;
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; uint8_t v___x_111_; lean_object* v_spawnArgs_112_; lean_object* v___x_113_; 
v___x_106_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0));
v___x_107_ = lean_box(0);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1));
v___x_110_ = 1;
v___x_111_ = 0;
lean_inc_ref(v_args_105_);
lean_inc_ref(v_lakePath_99_);
v_spawnArgs_112_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_spawnArgs_112_, 0, v___x_106_);
lean_ctor_set(v_spawnArgs_112_, 1, v_lakePath_99_);
lean_ctor_set(v_spawnArgs_112_, 2, v_args_105_);
lean_ctor_set(v_spawnArgs_112_, 3, v___x_107_);
lean_ctor_set(v_spawnArgs_112_, 4, v___x_109_);
lean_ctor_set_uint8(v_spawnArgs_112_, sizeof(void*)*5, v___x_110_);
lean_ctor_set_uint8(v_spawnArgs_112_, sizeof(void*)*5 + 1, v___x_111_);
lean_inc_ref(v_spawnArgs_112_);
v___x_113_ = lean_io_process_spawn(v_spawnArgs_112_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = lean_io_process_child_take_stdin(v___x_106_, v_a_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v_fst_117_ = lean_ctor_get(v_a_116_, 0);
lean_inc(v_fst_117_);
v_snd_118_ = lean_ctor_get(v_a_116_, 1);
lean_inc(v_snd_118_);
lean_dec(v_a_116_);
v___x_119_ = l_Lean_instToJsonModuleHeader_toJson(v_header_101_);
v___x_120_ = l_Lean_Json_compress(v___x_119_);
v___x_121_ = l_IO_FS_Handle_putStrLn(v_fst_117_, v___x_120_);
lean_dec(v_fst_117_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_stdout_125_; lean_object* v___x_126_; 
lean_dec_ref_known(v___x_121_, 1);
v___x_122_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
lean_inc(v_snd_118_);
v___x_123_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(v___x_123_, 0, v_lakePath_99_);
lean_closure_set(v___x_123_, 1, v_handleStderr_102_);
lean_closure_set(v___x_123_, 2, v_args_105_);
lean_closure_set(v___x_123_, 3, v_snd_118_);
lean_closure_set(v___x_123_, 4, v___x_122_);
v___x_124_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v___x_123_);
v_stdout_125_ = lean_ctor_get(v_snd_118_, 1);
v___x_126_ = l_IO_FS_Handle_readToEnd(v_stdout_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_str_131_; lean_object* v_startInclusive_132_; lean_object* v_endExclusive_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = lean_string_utf8_byte_size(v_a_127_);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v_a_127_);
lean_ctor_set(v___x_129_, 1, v___x_108_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
v___x_130_ = l_String_Slice_trimAscii(v___x_129_);
v_str_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc_ref(v_str_131_);
v_startInclusive_132_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_startInclusive_132_);
v_endExclusive_133_ = lean_ctor_get(v___x_130_, 2);
lean_inc(v_endExclusive_133_);
lean_dec_ref(v___x_130_);
v___x_134_ = lean_string_utf8_extract_fast(v_str_131_, v_startInclusive_132_, v_endExclusive_133_);
lean_dec(v_endExclusive_133_);
lean_dec(v_startInclusive_132_);
lean_dec_ref(v_str_131_);
v___x_135_ = lean_task_get_own(v___x_124_);
v___x_136_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v___x_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2));
v___x_139_ = lean_io_process_child_wait(v___x_138_, v_snd_118_);
lean_dec(v_snd_118_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_149_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; uint32_t v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_144_, 0, v_spawnArgs_112_);
lean_ctor_set(v___x_144_, 1, v___x_134_);
lean_ctor_set(v___x_144_, 2, v_a_137_);
v___x_145_ = lean_unbox_uint32(v_a_140_);
lean_dec(v_a_140_);
lean_ctor_set_uint32(v___x_144_, sizeof(void*)*3, v___x_145_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_144_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v_a_137_);
lean_dec_ref(v___x_134_);
lean_dec_ref_known(v_spawnArgs_112_, 5);
v_a_150_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_139_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_139_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
lean_dec_ref(v___x_134_);
lean_dec(v_snd_118_);
lean_dec_ref_known(v_spawnArgs_112_, 5);
v_a_158_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_136_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_136_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec_ref(v___x_124_);
lean_dec(v_snd_118_);
lean_dec_ref_known(v_spawnArgs_112_, 5);
v_a_166_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_126_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_126_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_snd_118_);
lean_dec_ref_known(v_spawnArgs_112_, 5);
lean_dec_ref(v_args_105_);
lean_dec_ref(v_handleStderr_102_);
lean_dec_ref(v_lakePath_99_);
v_a_174_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_121_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_121_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref_known(v_spawnArgs_112_, 5);
lean_dec_ref(v_args_105_);
lean_dec_ref(v_handleStderr_102_);
lean_dec_ref(v_header_101_);
lean_dec_ref(v_lakePath_99_);
v_a_182_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_115_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_115_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec_ref_known(v_spawnArgs_112_, 5);
lean_dec_ref(v_args_105_);
lean_dec_ref(v_handleStderr_102_);
lean_dec_ref(v_header_101_);
lean_dec_ref(v_lakePath_99_);
v_a_190_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_113_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_113_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_runLakeSetupFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_98_ = stack[0].m_obj;
lean_object* v_lakePath_99_ = stack[1].m_obj;
lean_object* v_filePath_100_ = stack[2].m_obj;
lean_object* v_header_101_ = stack[3].m_obj;
lean_object* v_handleStderr_102_ = stack[4].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_98_, v_lakePath_99_, v_filePath_100_, v_header_101_, v_handleStderr_102_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* v_m_208_, lean_object* v_lakePath_209_, lean_object* v_filePath_210_, lean_object* v_header_211_, lean_object* v_handleStderr_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_208_, v_lakePath_209_, v_filePath_210_, v_header_211_, v_handleStderr_212_);
lean_dec_ref(v_m_208_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl(lean_object* v_x_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_tag_nat(v_x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl___boxed(lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl(v_x_217_);
lean_dec(v_x_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object* v_t_219_, lean_object* v_k_220_){
_start:
{
switch(lean_obj_tag(v_t_219_))
{
case 0:
{
lean_object* v_setup_221_; lean_object* v___x_222_; 
v_setup_221_ = lean_ctor_get(v_t_219_, 0);
lean_inc_ref(v_setup_221_);
lean_dec_ref_known(v_t_219_, 1);
v___x_222_ = lean_apply_1(v_k_220_, v_setup_221_);
return v___x_222_;
}
case 3:
{
lean_object* v_msg_223_; lean_object* v___x_224_; 
v_msg_223_ = lean_ctor_get(v_t_219_, 0);
lean_inc_ref(v_msg_223_);
lean_dec_ref_known(v_t_219_, 1);
v___x_224_ = lean_apply_1(v_k_220_, v_msg_223_);
return v___x_224_;
}
default: 
{
lean_dec(v_t_219_);
return v_k_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object* v_motive_225_, lean_object* v_ctorIdx_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_k_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_227_, v_k_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object* v_motive_231_, lean_object* v_ctorIdx_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_k_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(v_motive_231_, v_ctorIdx_232_, v_t_233_, v_h_234_, v_k_235_);
lean_dec(v_ctorIdx_232_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object* v_t_237_, lean_object* v_success_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_237_, v_success_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object* v_motive_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_success_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_241_, v_success_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object* v_t_245_, lean_object* v_noLakefile_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_245_, v_noLakefile_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object* v_motive_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_noLakefile_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_249_, v_noLakefile_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object* v_t_253_, lean_object* v_importsOutOfDate_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_253_, v_importsOutOfDate_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object* v_motive_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_importsOutOfDate_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_257_, v_importsOutOfDate_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object* v_t_261_, lean_object* v_error_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_261_, v_error_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_error_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_265_, v_error_267_);
return v___x_268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object* v_as_269_, size_t v_i_270_, size_t v_stop_271_, lean_object* v_b_272_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_usize_dec_eq(v_i_270_, v_stop_271_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_array_uget_borrowed(v_as_269_, v_i_270_);
lean_inc(v___x_275_);
v___x_276_ = lean_load_dynlib(v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; size_t v___x_278_; size_t v___x_279_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_add(v_i_270_, v___x_278_);
v_i_270_ = v___x_279_;
v_b_272_ = v_a_277_;
goto _start;
}
else
{
return v___x_276_;
}
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v_b_272_);
return v___x_281_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_269_ = stack[0].m_obj;
size_t v_i_270_ = stack[1].m_num;
size_t v_stop_271_ = stack[2].m_num;
lean_object* v_b_272_ = stack[3].m_obj;
lean_object* v_res_282_;
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_269_, v_i_270_, v_stop_271_, v_b_272_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* v_as_283_, lean_object* v_i_284_, lean_object* v_stop_285_, lean_object* v_b_286_, lean_object* v___y_287_){
_start:
{
size_t v_i_boxed_288_; size_t v_stop_boxed_289_; lean_object* v_res_290_; 
v_i_boxed_288_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_stop_boxed_289_ = lean_unbox_usize(v_stop_285_);
lean_dec(v_stop_285_);
v_res_290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_283_, v_i_boxed_288_, v_stop_boxed_289_, v_b_286_);
lean_dec_ref(v_as_283_);
return v_res_290_;
}
}
lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* v_m_297_, lean_object* v_header_298_, lean_object* v_handleStderr_299_){
_start:
{
lean_object* v_uri_301_; lean_object* v___x_302_; 
v_uri_301_ = lean_ctor_get(v_m_297_, 0);
v___x_302_ = l_System_Uri_fileUriToPath_x3f(v_uri_301_);
if (lean_obj_tag(v___x_302_) == 1)
{
lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_428_; 
v_val_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_428_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_428_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_428_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_419_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_419_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_419_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_419_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = l_System_FilePath_pathExists(v_a_308_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_315_; 
lean_dec(v_a_308_);
lean_del_object(v___x_305_);
lean_dec(v_val_303_);
lean_dec_ref(v_handleStderr_299_);
lean_dec_ref(v_header_298_);
v___x_313_ = lean_box(1);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_313_);
v___x_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_297_, v_a_308_, v_val_303_, v_header_298_, v_handleStderr_299_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_410_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_410_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_410_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_410_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_spawnArgs_322_; uint32_t v_exitCode_323_; lean_object* v_stdout_324_; lean_object* v_stderr_325_; lean_object* v_cmd_326_; lean_object* v_args_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint32_t v___x_347_; uint8_t v___x_348_; 
v_spawnArgs_322_ = lean_ctor_get(v_a_318_, 0);
lean_inc_ref(v_spawnArgs_322_);
v_exitCode_323_ = lean_ctor_get_uint32(v_a_318_, sizeof(void*)*3);
v_stdout_324_ = lean_ctor_get(v_a_318_, 1);
lean_inc_ref(v_stdout_324_);
v_stderr_325_ = lean_ctor_get(v_a_318_, 2);
lean_inc_ref(v_stderr_325_);
lean_dec(v_a_318_);
v_cmd_326_ = lean_ctor_get(v_spawnArgs_322_, 1);
lean_inc_ref(v_cmd_326_);
v_args_327_ = lean_ctor_get(v_spawnArgs_322_, 2);
lean_inc_ref(v_args_327_);
lean_dec_ref(v_spawnArgs_322_);
v___x_328_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__0));
v___x_329_ = lean_array_to_list(v_args_327_);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v_cmd_326_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_String_intercalate(v___x_328_, v___x_330_);
v___x_347_ = 0;
v___x_348_ = lean_uint32_dec_eq(v_exitCode_323_, v___x_347_);
if (v___x_348_ == 0)
{
uint32_t v___x_349_; uint8_t v___x_350_; 
lean_del_object(v___x_320_);
lean_del_object(v___x_305_);
v___x_349_ = 2;
v___x_350_ = lean_uint32_dec_eq(v_exitCode_323_, v___x_349_);
if (v___x_350_ == 0)
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 3;
v___x_352_ = lean_uint32_dec_eq(v_exitCode_323_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_353_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__4));
v___x_354_ = lean_string_append(v___x_353_, v___x_331_);
lean_dec_ref(v___x_331_);
v___x_355_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__5));
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
v___x_357_ = lean_string_append(v___x_356_, v_stdout_324_);
lean_dec_ref(v_stdout_324_);
v___x_358_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
v___x_360_ = lean_string_append(v___x_359_, v_stderr_325_);
lean_dec_ref(v_stderr_325_);
v___x_361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_361_);
v___x_363_ = v___x_310_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v_stderr_325_);
lean_dec_ref(v_stdout_324_);
v___x_365_ = lean_box(2);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_365_);
v___x_367_ = v___x_310_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v_stderr_325_);
lean_dec_ref(v_stdout_324_);
v___x_369_ = lean_box(1);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_369_);
v___x_371_ = v___x_310_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v___x_373_; 
lean_inc_ref(v_stdout_324_);
v___x_373_ = l_Lean_Json_parse(v_stdout_324_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_dec_ref_known(v___x_373_, 1);
lean_del_object(v___x_310_);
goto v___jp_332_;
}
else
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_374_);
if (lean_obj_tag(v___x_375_) == 1)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v_stderr_325_);
lean_dec_ref(v_stdout_324_);
lean_del_object(v___x_320_);
lean_del_object(v___x_305_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_409_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_409_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_409_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___y_388_; lean_object* v_dynlibs_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_dynlibs_397_ = lean_ctor_get(v_a_376_, 4);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_array_get_size(v_dynlibs_397_);
v___x_400_ = lean_nat_dec_lt(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
goto v___jp_380_;
}
else
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_nat_dec_le(v___x_399_, v___x_399_);
if (v___x_402_ == 0)
{
if (v___x_400_ == 0)
{
goto v___jp_380_;
}
else
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((size_t)0ULL);
v___x_404_ = lean_usize_of_nat(v___x_399_);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_397_, v___x_403_, v___x_404_, v___x_401_);
v___y_388_ = v___x_405_;
goto v___jp_387_;
}
}
else
{
size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_406_ = ((size_t)0ULL);
v___x_407_ = lean_usize_of_nat(v___x_399_);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_397_, v___x_406_, v___x_407_, v___x_401_);
v___y_388_ = v___x_408_;
goto v___jp_387_;
}
}
v___jp_380_:
{
lean_object* v___x_382_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 0);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_376_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_382_);
v___x_384_ = v___x_310_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
v___jp_387_:
{
if (lean_obj_tag(v___y_388_) == 0)
{
lean_dec_ref_known(v___y_388_, 1);
goto v___jp_380_;
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_del_object(v___x_378_);
lean_dec(v_a_376_);
lean_del_object(v___x_310_);
v_a_389_ = lean_ctor_get(v___y_388_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___y_388_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___y_388_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___y_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_375_);
lean_del_object(v___x_310_);
goto v___jp_332_;
}
}
}
v___jp_332_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_333_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__1));
v___x_334_ = lean_string_append(v___x_333_, v___x_331_);
lean_dec_ref(v___x_331_);
v___x_335_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__2));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
v___x_337_ = lean_string_append(v___x_336_, v_stdout_324_);
lean_dec_ref(v_stdout_324_);
v___x_338_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_339_ = lean_string_append(v___x_337_, v___x_338_);
v___x_340_ = lean_string_append(v___x_339_, v_stderr_325_);
lean_dec_ref(v_stderr_325_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 3);
lean_ctor_set(v___x_305_, 0, v___x_340_);
v___x_342_ = v___x_305_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_342_);
v___x_344_ = v___x_320_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_del_object(v___x_310_);
lean_del_object(v___x_305_);
v_a_411_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_317_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_317_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_del_object(v___x_305_);
lean_dec(v_val_303_);
lean_dec_ref(v_handleStderr_299_);
lean_dec_ref(v_header_298_);
v_a_420_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_307_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_307_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v___x_302_);
lean_dec_ref(v_handleStderr_299_);
lean_dec_ref(v_header_298_);
v___x_429_ = lean_box(1);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_setupFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_297_ = stack[0].m_obj;
lean_object* v_header_298_ = stack[1].m_obj;
lean_object* v_handleStderr_299_ = stack[2].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_Lean_Server_FileWorker_setupFile(v_m_297_, v_header_298_, v_handleStderr_299_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object* v_m_432_, lean_object* v_header_433_, lean_object* v_handleStderr_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Server_FileWorker_setupFile(v_m_432_, v_header_433_, v_handleStderr_434_);
lean_dec_ref(v_m_432_);
return v_res_436_;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SetupFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_SetupFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_SetupFile(builtin);
}
#ifdef __cplusplus
}
#endif
