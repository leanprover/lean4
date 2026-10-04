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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* v_handleStderr_2_, lean_object* v_lakeProc_3_, lean_object* v_acc_4_){
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* v_handleStderr_29_, lean_object* v_lakeProc_30_, lean_object* v_acc_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_29_, v_lakeProc_30_, v_acc_31_);
lean_dec_ref(v_lakeProc_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* v_lakePath_34_, lean_object* v_handleStderr_35_, lean_object* v_args_36_, lean_object* v_lakeProc_37_, lean_object* v_acc_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_35_, v_lakeProc_37_, v_acc_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* v_lakePath_41_, lean_object* v_handleStderr_42_, lean_object* v_args_43_, lean_object* v_lakeProc_44_, lean_object* v_acc_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(v_lakePath_41_, v_handleStderr_42_, v_args_43_, v_lakeProc_44_, v_acc_45_);
lean_dec_ref(v_lakeProc_44_);
lean_dec_ref(v_args_43_);
lean_dec_ref(v_lakePath_41_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object* v_e_48_){
_start:
{
if (lean_obj_tag(v_e_48_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_59_; 
v_a_50_ = lean_ctor_get(v_e_48_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v_e_48_);
if (v_isSharedCheck_59_ == 0)
{
v___x_52_ = v_e_48_;
v_isShared_53_ = v_isSharedCheck_59_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v_e_48_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_59_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_54_ = lean_io_error_to_string(v_a_50_);
v___x_55_ = lean_mk_io_user_error(v___x_54_);
if (v_isShared_53_ == 0)
{
lean_ctor_set_tag(v___x_52_, 1);
lean_ctor_set(v___x_52_, 0, v___x_55_);
v___x_57_ = v___x_52_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v_e_48_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_e_48_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_e_48_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v_e_48_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 0);
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(lean_object* v_e_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object* v_00_u03b1_71_, lean_object* v_e_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object* v_00_u03b1_75_, lean_object* v_e_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(v_00_u03b1_75_, v_e_76_);
return v_res_78_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3));
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_89_);
v___x_91_ = lean_array_push(v___x_90_, v___x_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* v_m_94_, lean_object* v_lakePath_95_, lean_object* v_filePath_96_, lean_object* v_header_97_, lean_object* v_handleStderr_98_){
_start:
{
lean_object* v_args_101_; uint8_t v_dependencyBuildMode_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_args_198_; 
v_dependencyBuildMode_194_ = lean_ctor_get_uint8(v_m_94_, sizeof(void*)*4);
v___x_195_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4));
v___x_196_ = lean_obj_once(&l_Lean_Server_FileWorker_runLakeSetupFile___closed__5, &l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once, _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
v___x_197_ = lean_array_push(v___x_196_, v_filePath_96_);
v_args_198_ = lean_array_push(v___x_197_, v___x_195_);
if (v_dependencyBuildMode_194_ == 2)
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_args_202_; 
v___x_199_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6));
v___x_200_ = lean_array_push(v_args_198_, v___x_199_);
v___x_201_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7));
v_args_202_ = lean_array_push(v___x_200_, v___x_201_);
v_args_101_ = v_args_202_;
goto v___jp_100_;
}
else
{
v_args_101_ = v_args_198_;
goto v___jp_100_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; uint8_t v___x_107_; lean_object* v_spawnArgs_108_; lean_object* v___x_109_; 
v___x_102_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0));
v___x_103_ = lean_box(0);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1));
v___x_106_ = 1;
v___x_107_ = 0;
lean_inc_ref(v_args_101_);
lean_inc_ref(v_lakePath_95_);
v_spawnArgs_108_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_spawnArgs_108_, 0, v___x_102_);
lean_ctor_set(v_spawnArgs_108_, 1, v_lakePath_95_);
lean_ctor_set(v_spawnArgs_108_, 2, v_args_101_);
lean_ctor_set(v_spawnArgs_108_, 3, v___x_103_);
lean_ctor_set(v_spawnArgs_108_, 4, v___x_105_);
lean_ctor_set_uint8(v_spawnArgs_108_, sizeof(void*)*5, v___x_106_);
lean_ctor_set_uint8(v_spawnArgs_108_, sizeof(void*)*5 + 1, v___x_107_);
lean_inc_ref(v_spawnArgs_108_);
v___x_109_ = lean_io_process_spawn(v_spawnArgs_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
v___x_111_ = lean_io_process_child_take_stdin(v___x_102_, v_a_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v_fst_113_ = lean_ctor_get(v_a_112_, 0);
lean_inc(v_fst_113_);
v_snd_114_ = lean_ctor_get(v_a_112_, 1);
lean_inc(v_snd_114_);
lean_dec(v_a_112_);
v___x_115_ = l_Lean_instToJsonModuleHeader_toJson(v_header_97_);
v___x_116_ = l_Lean_Json_compress(v___x_115_);
v___x_117_ = l_IO_FS_Handle_putStrLn(v_fst_113_, v___x_116_);
lean_dec(v_fst_113_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_stdout_121_; lean_object* v___x_122_; 
lean_dec_ref_known(v___x_117_, 1);
v___x_118_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0));
lean_inc(v_snd_114_);
v___x_119_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(v___x_119_, 0, v_lakePath_95_);
lean_closure_set(v___x_119_, 1, v_handleStderr_98_);
lean_closure_set(v___x_119_, 2, v_args_101_);
lean_closure_set(v___x_119_, 3, v_snd_114_);
lean_closure_set(v___x_119_, 4, v___x_118_);
v___x_120_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v___x_119_);
v_stdout_121_ = lean_ctor_get(v_snd_114_, 1);
v___x_122_ = l_IO_FS_Handle_readToEnd(v_stdout_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_str_127_; lean_object* v_startInclusive_128_; lean_object* v_endExclusive_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = lean_string_utf8_byte_size(v_a_123_);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v_a_123_);
lean_ctor_set(v___x_125_, 1, v___x_104_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
v___x_126_ = l_String_Slice_trimAscii(v___x_125_);
v_str_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_str_127_);
v_startInclusive_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_startInclusive_128_);
v_endExclusive_129_ = lean_ctor_get(v___x_126_, 2);
lean_inc(v_endExclusive_129_);
lean_dec_ref(v___x_126_);
v___x_130_ = lean_string_utf8_extract_fast(v_str_127_, v_startInclusive_128_, v_endExclusive_129_);
lean_dec(v_endExclusive_129_);
lean_dec(v_startInclusive_128_);
lean_dec_ref(v_str_127_);
v___x_131_ = lean_task_get_own(v___x_120_);
v___x_132_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v___x_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_132_, 1);
v___x_134_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2));
v___x_135_ = lean_io_process_child_wait(v___x_134_, v_snd_114_);
lean_dec(v_snd_114_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_145_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_145_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; uint32_t v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_140_, 0, v_spawnArgs_108_);
lean_ctor_set(v___x_140_, 1, v___x_130_);
lean_ctor_set(v___x_140_, 2, v_a_133_);
v___x_141_ = lean_unbox_uint32(v_a_136_);
lean_dec(v_a_136_);
lean_ctor_set_uint32(v___x_140_, sizeof(void*)*3, v___x_141_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_140_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_140_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_a_133_);
lean_dec_ref(v___x_130_);
lean_dec_ref_known(v_spawnArgs_108_, 5);
v_a_146_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_135_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_135_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v___x_130_);
lean_dec(v_snd_114_);
lean_dec_ref_known(v_spawnArgs_108_, 5);
v_a_154_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_132_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_132_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v___x_120_);
lean_dec(v_snd_114_);
lean_dec_ref_known(v_spawnArgs_108_, 5);
v_a_162_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_122_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_122_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec(v_snd_114_);
lean_dec_ref_known(v_spawnArgs_108_, 5);
lean_dec_ref(v_args_101_);
lean_dec_ref(v_handleStderr_98_);
lean_dec_ref(v_lakePath_95_);
v_a_170_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_117_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_117_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref_known(v_spawnArgs_108_, 5);
lean_dec_ref(v_args_101_);
lean_dec_ref(v_handleStderr_98_);
lean_dec_ref(v_header_97_);
lean_dec_ref(v_lakePath_95_);
v_a_178_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_111_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_111_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec_ref_known(v_spawnArgs_108_, 5);
lean_dec_ref(v_args_101_);
lean_dec_ref(v_handleStderr_98_);
lean_dec_ref(v_header_97_);
lean_dec_ref(v_lakePath_95_);
v_a_186_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_109_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_109_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* v_m_203_, lean_object* v_lakePath_204_, lean_object* v_filePath_205_, lean_object* v_header_206_, lean_object* v_handleStderr_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_203_, v_lakePath_204_, v_filePath_205_, v_header_206_, v_handleStderr_207_);
lean_dec_ref(v_m_203_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl(lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_tag_nat(v_x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl___boxed(lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___impl(v_x_212_);
lean_dec(v_x_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object* v_t_214_, lean_object* v_k_215_){
_start:
{
switch(lean_obj_tag(v_t_214_))
{
case 0:
{
lean_object* v_setup_216_; lean_object* v___x_217_; 
v_setup_216_ = lean_ctor_get(v_t_214_, 0);
lean_inc_ref(v_setup_216_);
lean_dec_ref_known(v_t_214_, 1);
v___x_217_ = lean_apply_1(v_k_215_, v_setup_216_);
return v___x_217_;
}
case 3:
{
lean_object* v_msg_218_; lean_object* v___x_219_; 
v_msg_218_ = lean_ctor_get(v_t_214_, 0);
lean_inc_ref(v_msg_218_);
lean_dec_ref_known(v_t_214_, 1);
v___x_219_ = lean_apply_1(v_k_215_, v_msg_218_);
return v___x_219_;
}
default: 
{
lean_dec(v_t_214_);
return v_k_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object* v_motive_220_, lean_object* v_ctorIdx_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_222_, v_k_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object* v_motive_226_, lean_object* v_ctorIdx_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_k_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(v_motive_226_, v_ctorIdx_227_, v_t_228_, v_h_229_, v_k_230_);
lean_dec(v_ctorIdx_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object* v_t_232_, lean_object* v_success_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_232_, v_success_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object* v_motive_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_success_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_236_, v_success_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object* v_t_240_, lean_object* v_noLakefile_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_240_, v_noLakefile_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_noLakefile_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_244_, v_noLakefile_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object* v_t_248_, lean_object* v_importsOutOfDate_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_248_, v_importsOutOfDate_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object* v_motive_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_importsOutOfDate_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_252_, v_importsOutOfDate_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object* v_t_256_, lean_object* v_error_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_256_, v_error_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_error_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_260_, v_error_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object* v_as_264_, size_t v_i_265_, size_t v_stop_266_, lean_object* v_b_267_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_eq(v_i_265_, v_stop_266_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_array_uget_borrowed(v_as_264_, v_i_265_);
lean_inc(v___x_270_);
v___x_271_ = lean_load_dynlib(v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; size_t v___x_273_; size_t v___x_274_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = lean_usize_add(v_i_265_, v___x_273_);
v_i_265_ = v___x_274_;
v_b_267_ = v_a_272_;
goto _start;
}
else
{
return v___x_271_;
}
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_b_267_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* v_as_277_, lean_object* v_i_278_, lean_object* v_stop_279_, lean_object* v_b_280_, lean_object* v___y_281_){
_start:
{
size_t v_i_boxed_282_; size_t v_stop_boxed_283_; lean_object* v_res_284_; 
v_i_boxed_282_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_stop_boxed_283_ = lean_unbox_usize(v_stop_279_);
lean_dec(v_stop_279_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_277_, v_i_boxed_282_, v_stop_boxed_283_, v_b_280_);
lean_dec_ref(v_as_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* v_m_291_, lean_object* v_header_292_, lean_object* v_handleStderr_293_){
_start:
{
lean_object* v_uri_295_; lean_object* v___x_296_; 
v_uri_295_ = lean_ctor_get(v_m_291_, 0);
v___x_296_ = l_System_Uri_fileUriToPath_x3f(v_uri_295_);
if (lean_obj_tag(v___x_296_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_422_; 
v_val_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_422_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_422_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_422_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_413_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_413_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_413_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_413_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint8_t v___x_306_; 
v___x_306_ = l_System_FilePath_pathExists(v_a_302_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v_a_302_);
lean_del_object(v___x_299_);
lean_dec(v_val_297_);
lean_dec_ref(v_handleStderr_293_);
lean_dec_ref(v_header_292_);
v___x_307_ = lean_box(1);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_291_, v_a_302_, v_val_297_, v_header_292_, v_handleStderr_293_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_404_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_404_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_404_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_404_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_spawnArgs_316_; uint32_t v_exitCode_317_; lean_object* v_stdout_318_; lean_object* v_stderr_319_; lean_object* v_cmd_320_; lean_object* v_args_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint32_t v___x_341_; uint8_t v___x_342_; 
v_spawnArgs_316_ = lean_ctor_get(v_a_312_, 0);
lean_inc_ref(v_spawnArgs_316_);
v_exitCode_317_ = lean_ctor_get_uint32(v_a_312_, sizeof(void*)*3);
v_stdout_318_ = lean_ctor_get(v_a_312_, 1);
lean_inc_ref(v_stdout_318_);
v_stderr_319_ = lean_ctor_get(v_a_312_, 2);
lean_inc_ref(v_stderr_319_);
lean_dec(v_a_312_);
v_cmd_320_ = lean_ctor_get(v_spawnArgs_316_, 1);
lean_inc_ref(v_cmd_320_);
v_args_321_ = lean_ctor_get(v_spawnArgs_316_, 2);
lean_inc_ref(v_args_321_);
lean_dec_ref(v_spawnArgs_316_);
v___x_322_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__0));
v___x_323_ = lean_array_to_list(v_args_321_);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v_cmd_320_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = l_String_intercalate(v___x_322_, v___x_324_);
v___x_341_ = 0;
v___x_342_ = lean_uint32_dec_eq(v_exitCode_317_, v___x_341_);
if (v___x_342_ == 0)
{
uint32_t v___x_343_; uint8_t v___x_344_; 
lean_del_object(v___x_314_);
lean_del_object(v___x_299_);
v___x_343_ = 2;
v___x_344_ = lean_uint32_dec_eq(v_exitCode_317_, v___x_343_);
if (v___x_344_ == 0)
{
uint32_t v___x_345_; uint8_t v___x_346_; 
v___x_345_ = 3;
v___x_346_ = lean_uint32_dec_eq(v_exitCode_317_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_347_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__4));
v___x_348_ = lean_string_append(v___x_347_, v___x_325_);
lean_dec_ref(v___x_325_);
v___x_349_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__5));
v___x_350_ = lean_string_append(v___x_348_, v___x_349_);
v___x_351_ = lean_string_append(v___x_350_, v_stdout_318_);
lean_dec_ref(v_stdout_318_);
v___x_352_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___x_354_ = lean_string_append(v___x_353_, v_stderr_319_);
lean_dec_ref(v_stderr_319_);
v___x_355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_355_);
v___x_357_ = v___x_304_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec_ref(v___x_325_);
lean_dec_ref(v_stderr_319_);
lean_dec_ref(v_stdout_318_);
v___x_359_ = lean_box(2);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_359_);
v___x_361_ = v___x_304_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_365_; 
lean_dec_ref(v___x_325_);
lean_dec_ref(v_stderr_319_);
lean_dec_ref(v_stdout_318_);
v___x_363_ = lean_box(1);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_363_);
v___x_365_ = v___x_304_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v___x_367_; 
lean_inc_ref(v_stdout_318_);
v___x_367_ = l_Lean_Json_parse(v_stdout_318_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_dec_ref_known(v___x_367_, 1);
lean_del_object(v___x_304_);
goto v___jp_326_;
}
else
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_368_);
if (lean_obj_tag(v___x_369_) == 1)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v___x_325_);
lean_dec_ref(v_stderr_319_);
lean_dec_ref(v_stdout_318_);
lean_del_object(v___x_314_);
lean_del_object(v___x_299_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_403_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_403_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_403_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___y_382_; lean_object* v_dynlibs_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_dynlibs_391_ = lean_ctor_get(v_a_370_, 4);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_array_get_size(v_dynlibs_391_);
v___x_394_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
goto v___jp_374_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_nat_dec_le(v___x_393_, v___x_393_);
if (v___x_396_ == 0)
{
if (v___x_394_ == 0)
{
goto v___jp_374_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_393_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_391_, v___x_397_, v___x_398_, v___x_395_);
v___y_382_ = v___x_399_;
goto v___jp_381_;
}
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_393_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_391_, v___x_400_, v___x_401_, v___x_395_);
v___y_382_ = v___x_402_;
goto v___jp_381_;
}
}
v___jp_374_:
{
lean_object* v___x_376_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 0);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_370_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_376_);
v___x_378_ = v___x_304_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
v___jp_381_:
{
if (lean_obj_tag(v___y_382_) == 0)
{
lean_dec_ref_known(v___y_382_, 1);
goto v___jp_374_;
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_372_);
lean_dec(v_a_370_);
lean_del_object(v___x_304_);
v_a_383_ = lean_ctor_get(v___y_382_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___y_382_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___y_382_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___y_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_369_);
lean_del_object(v___x_304_);
goto v___jp_326_;
}
}
}
v___jp_326_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_327_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__1));
v___x_328_ = lean_string_append(v___x_327_, v___x_325_);
lean_dec_ref(v___x_325_);
v___x_329_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__2));
v___x_330_ = lean_string_append(v___x_328_, v___x_329_);
v___x_331_ = lean_string_append(v___x_330_, v_stdout_318_);
lean_dec_ref(v_stdout_318_);
v___x_332_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_string_append(v___x_333_, v_stderr_319_);
lean_dec_ref(v_stderr_319_);
if (v_isShared_300_ == 0)
{
lean_ctor_set_tag(v___x_299_, 3);
lean_ctor_set(v___x_299_, 0, v___x_334_);
v___x_336_ = v___x_299_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_336_);
v___x_338_ = v___x_314_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_del_object(v___x_304_);
lean_del_object(v___x_299_);
v_a_405_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_311_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_311_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_del_object(v___x_299_);
lean_dec(v_val_297_);
lean_dec_ref(v_handleStderr_293_);
lean_dec_ref(v_header_292_);
v_a_414_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_301_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_301_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v___x_296_);
lean_dec_ref(v_handleStderr_293_);
lean_dec_ref(v_header_292_);
v___x_423_ = lean_box(1);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object* v_m_425_, lean_object* v_header_426_, lean_object* v_handleStderr_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Server_FileWorker_setupFile(v_m_425_, v_header_426_, v_handleStderr_427_);
lean_dec_ref(v_m_425_);
return v_res_429_;
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
