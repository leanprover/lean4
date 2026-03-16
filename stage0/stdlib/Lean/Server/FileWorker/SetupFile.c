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
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object*);
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
lean_dec_ref(v___x_14_);
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
lean_object* v_args_101_; uint8_t v_dependencyBuildMode_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_args_207_; 
v_dependencyBuildMode_203_ = lean_ctor_get_uint8(v_m_94_, sizeof(void*)*4);
v___x_204_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4));
v___x_205_ = lean_obj_once(&l_Lean_Server_FileWorker_runLakeSetupFile___closed__5, &l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once, _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
v___x_206_ = lean_array_push(v___x_205_, v_filePath_96_);
v_args_207_ = lean_array_push(v___x_206_, v___x_204_);
if (v_dependencyBuildMode_203_ == 2)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_args_211_; 
v___x_208_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6));
v___x_209_ = lean_array_push(v_args_207_, v___x_208_);
v___x_210_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7));
v_args_211_ = lean_array_push(v___x_209_, v___x_210_);
v_args_101_ = v_args_211_;
goto v___jp_100_;
}
else
{
v_args_101_ = v_args_207_;
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
lean_dec_ref(v___x_109_);
v___x_111_ = lean_io_process_child_take_stdin(v___x_102_, v_a_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v___x_111_);
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
lean_dec_ref(v___x_117_);
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
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref(v___x_122_);
v___x_124_ = lean_task_get_own(v___x_120_);
v___x_125_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v___x_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_159_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref(v___x_125_);
v___x_127_ = ((lean_object*)(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2));
v___x_128_ = lean_io_process_child_wait(v___x_127_, v_snd_114_);
v_isSharedCheck_159_ = !lean_is_exclusive(v_snd_114_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_160_ = lean_ctor_get(v_snd_114_, 2);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_snd_114_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_snd_114_, 0);
lean_dec(v_unused_162_);
v___x_130_ = v_snd_114_;
v_isShared_131_ = v_isSharedCheck_159_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_snd_114_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_159_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_150_; 
v_a_132_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_150_ == 0)
{
v___x_134_ = v___x_128_;
v_isShared_135_ = v_isSharedCheck_150_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_128_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_150_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_string_utf8_byte_size(v_a_123_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 2, v___x_136_);
lean_ctor_set(v___x_130_, 1, v___x_104_);
lean_ctor_set(v___x_130_, 0, v_a_123_);
v___x_138_ = v___x_130_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_123_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v___x_136_);
v___x_138_ = v_reuseFailAlloc_149_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v_str_140_; lean_object* v_startInclusive_141_; lean_object* v_endExclusive_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint32_t v___x_145_; lean_object* v___x_147_; 
v___x_139_ = l_String_Slice_trimAscii(v___x_138_);
lean_dec_ref(v___x_138_);
v_str_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_str_140_);
v_startInclusive_141_ = lean_ctor_get(v___x_139_, 1);
lean_inc(v_startInclusive_141_);
v_endExclusive_142_ = lean_ctor_get(v___x_139_, 2);
lean_inc(v_endExclusive_142_);
lean_dec_ref(v___x_139_);
v___x_143_ = lean_string_utf8_extract(v_str_140_, v_startInclusive_141_, v_endExclusive_142_);
lean_dec(v_endExclusive_142_);
lean_dec(v_startInclusive_141_);
lean_dec_ref(v_str_140_);
v___x_144_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_144_, 0, v_spawnArgs_108_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set(v___x_144_, 2, v_a_126_);
v___x_145_ = lean_unbox_uint32(v_a_132_);
lean_dec(v_a_132_);
lean_ctor_set_uint32(v___x_144_, sizeof(void*)*3, v___x_145_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_144_);
v___x_147_ = v___x_134_;
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
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_del_object(v___x_130_);
lean_dec(v_a_126_);
lean_dec(v_a_123_);
lean_dec_ref(v_spawnArgs_108_);
v_a_151_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_128_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_128_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec(v_a_123_);
lean_dec(v_snd_114_);
lean_dec_ref(v_spawnArgs_108_);
v_a_163_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_125_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_125_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v___x_120_);
lean_dec(v_snd_114_);
lean_dec_ref(v_spawnArgs_108_);
v_a_171_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_122_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_122_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_snd_114_);
lean_dec_ref(v_spawnArgs_108_);
lean_dec_ref(v_args_101_);
lean_dec_ref(v_handleStderr_98_);
lean_dec_ref(v_lakePath_95_);
v_a_179_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_117_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_117_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec_ref(v_spawnArgs_108_);
lean_dec_ref(v_args_101_);
lean_dec_ref(v_handleStderr_98_);
lean_dec_ref(v_header_97_);
lean_dec_ref(v_lakePath_95_);
v_a_187_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_111_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_111_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec_ref(v_spawnArgs_108_);
lean_dec_ref(v_args_101_);
lean_dec_ref(v_handleStderr_98_);
lean_dec_ref(v_header_97_);
lean_dec_ref(v_lakePath_95_);
v_a_195_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_109_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_109_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* v_m_212_, lean_object* v_lakePath_213_, lean_object* v_filePath_214_, lean_object* v_header_215_, lean_object* v_handleStderr_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_212_, v_lakePath_213_, v_filePath_214_, v_header_215_, v_handleStderr_216_);
lean_dec_ref(v_m_212_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object* v_x_219_){
_start:
{
switch(lean_obj_tag(v_x_219_))
{
case 0:
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(0u);
return v___x_220_;
}
case 1:
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(1u);
return v___x_221_;
}
case 2:
{
lean_object* v___x_222_; 
v___x_222_ = lean_unsigned_to_nat(2u);
return v___x_222_;
}
default: 
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(3u);
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object* v_t_226_, lean_object* v_k_227_){
_start:
{
switch(lean_obj_tag(v_t_226_))
{
case 0:
{
lean_object* v_setup_228_; lean_object* v___x_229_; 
v_setup_228_ = lean_ctor_get(v_t_226_, 0);
lean_inc_ref(v_setup_228_);
lean_dec_ref(v_t_226_);
v___x_229_ = lean_apply_1(v_k_227_, v_setup_228_);
return v___x_229_;
}
case 3:
{
lean_object* v_msg_230_; lean_object* v___x_231_; 
v_msg_230_ = lean_ctor_get(v_t_226_, 0);
lean_inc_ref(v_msg_230_);
lean_dec_ref(v_t_226_);
v___x_231_ = lean_apply_1(v_k_227_, v_msg_230_);
return v___x_231_;
}
default: 
{
lean_dec(v_t_226_);
return v_k_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object* v_motive_232_, lean_object* v_ctorIdx_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_k_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_234_, v_k_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object* v_motive_238_, lean_object* v_ctorIdx_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_k_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(v_motive_238_, v_ctorIdx_239_, v_t_240_, v_h_241_, v_k_242_);
lean_dec(v_ctorIdx_239_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object* v_t_244_, lean_object* v_success_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_244_, v_success_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object* v_motive_247_, lean_object* v_t_248_, lean_object* v_h_249_, lean_object* v_success_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_248_, v_success_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object* v_t_252_, lean_object* v_noLakefile_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_252_, v_noLakefile_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object* v_motive_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_noLakefile_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_256_, v_noLakefile_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object* v_t_260_, lean_object* v_importsOutOfDate_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_260_, v_importsOutOfDate_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_importsOutOfDate_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_264_, v_importsOutOfDate_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object* v_t_268_, lean_object* v_error_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_268_, v_error_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object* v_motive_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_error_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_272_, v_error_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object* v_as_276_, size_t v_i_277_, size_t v_stop_278_, lean_object* v_b_279_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_usize_dec_eq(v_i_277_, v_stop_278_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_array_uget_borrowed(v_as_276_, v_i_277_);
lean_inc(v___x_282_);
v___x_283_ = lean_load_dynlib(v___x_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; size_t v___x_285_; size_t v___x_286_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v___x_283_);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_add(v_i_277_, v___x_285_);
v_i_277_ = v___x_286_;
v_b_279_ = v_a_284_;
goto _start;
}
else
{
return v___x_283_;
}
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v_b_279_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* v_as_289_, lean_object* v_i_290_, lean_object* v_stop_291_, lean_object* v_b_292_, lean_object* v___y_293_){
_start:
{
size_t v_i_boxed_294_; size_t v_stop_boxed_295_; lean_object* v_res_296_; 
v_i_boxed_294_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_stop_boxed_295_ = lean_unbox_usize(v_stop_291_);
lean_dec(v_stop_291_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_289_, v_i_boxed_294_, v_stop_boxed_295_, v_b_292_);
lean_dec_ref(v_as_289_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* v_m_303_, lean_object* v_header_304_, lean_object* v_handleStderr_305_){
_start:
{
lean_object* v_uri_307_; lean_object* v___x_308_; 
v_uri_307_ = lean_ctor_get(v_m_303_, 0);
v___x_308_ = l_System_Uri_fileUriToPath_x3f(v_uri_307_);
if (lean_obj_tag(v___x_308_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_434_; 
v_val_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_434_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_434_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_434_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_425_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_425_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_425_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_425_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint8_t v___x_318_; 
v___x_318_ = l_System_FilePath_pathExists(v_a_314_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v_a_314_);
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_handleStderr_305_);
lean_dec_ref(v_header_304_);
v___x_319_ = lean_box(1);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_321_ = v___x_316_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_303_, v_a_314_, v_val_309_, v_header_304_, v_handleStderr_305_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_416_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_416_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_416_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_416_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_spawnArgs_328_; uint32_t v_exitCode_329_; lean_object* v_stdout_330_; lean_object* v_stderr_331_; lean_object* v_cmd_332_; lean_object* v_args_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint32_t v___x_353_; uint8_t v___x_354_; 
v_spawnArgs_328_ = lean_ctor_get(v_a_324_, 0);
lean_inc_ref(v_spawnArgs_328_);
v_exitCode_329_ = lean_ctor_get_uint32(v_a_324_, sizeof(void*)*3);
v_stdout_330_ = lean_ctor_get(v_a_324_, 1);
lean_inc_ref(v_stdout_330_);
v_stderr_331_ = lean_ctor_get(v_a_324_, 2);
lean_inc_ref(v_stderr_331_);
lean_dec(v_a_324_);
v_cmd_332_ = lean_ctor_get(v_spawnArgs_328_, 1);
lean_inc_ref(v_cmd_332_);
v_args_333_ = lean_ctor_get(v_spawnArgs_328_, 2);
lean_inc_ref(v_args_333_);
lean_dec_ref(v_spawnArgs_328_);
v___x_334_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__0));
v___x_335_ = lean_array_to_list(v_args_333_);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v_cmd_332_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_String_intercalate(v___x_334_, v___x_336_);
v___x_353_ = 0;
v___x_354_ = lean_uint32_dec_eq(v_exitCode_329_, v___x_353_);
if (v___x_354_ == 0)
{
uint32_t v___x_355_; uint8_t v___x_356_; 
lean_del_object(v___x_326_);
lean_del_object(v___x_311_);
v___x_355_ = 2;
v___x_356_ = lean_uint32_dec_eq(v_exitCode_329_, v___x_355_);
if (v___x_356_ == 0)
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 3;
v___x_358_ = lean_uint32_dec_eq(v_exitCode_329_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_359_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__4));
v___x_360_ = lean_string_append(v___x_359_, v___x_337_);
lean_dec_ref(v___x_337_);
v___x_361_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__5));
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
v___x_363_ = lean_string_append(v___x_362_, v_stdout_330_);
lean_dec_ref(v_stdout_330_);
v___x_364_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_365_ = lean_string_append(v___x_363_, v___x_364_);
v___x_366_ = lean_string_append(v___x_365_, v_stderr_331_);
lean_dec_ref(v_stderr_331_);
v___x_367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_367_);
v___x_369_ = v___x_316_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_stderr_331_);
lean_dec_ref(v_stdout_330_);
v___x_371_ = lean_box(2);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_371_);
v___x_373_ = v___x_316_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_377_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_stderr_331_);
lean_dec_ref(v_stdout_330_);
v___x_375_ = lean_box(1);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_375_);
v___x_377_ = v___x_316_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_inc_ref(v_stdout_330_);
v___x_379_ = l_Lean_Json_parse(v_stdout_330_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_dec_ref(v___x_379_);
lean_del_object(v___x_316_);
goto v___jp_338_;
}
else
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v___x_379_);
v___x_381_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_380_);
if (lean_obj_tag(v___x_381_) == 1)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_stderr_331_);
lean_dec_ref(v_stdout_330_);
lean_del_object(v___x_326_);
lean_del_object(v___x_311_);
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_415_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_415_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_415_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___y_394_; lean_object* v_dynlibs_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v_dynlibs_403_ = lean_ctor_get(v_a_382_, 4);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_array_get_size(v_dynlibs_403_);
v___x_406_ = lean_nat_dec_lt(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
goto v___jp_386_;
}
else
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_box(0);
v___x_408_ = lean_nat_dec_le(v___x_405_, v___x_405_);
if (v___x_408_ == 0)
{
if (v___x_406_ == 0)
{
goto v___jp_386_;
}
else
{
size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((size_t)0ULL);
v___x_410_ = lean_usize_of_nat(v___x_405_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_403_, v___x_409_, v___x_410_, v___x_407_);
v___y_394_ = v___x_411_;
goto v___jp_393_;
}
}
else
{
size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v___x_412_ = ((size_t)0ULL);
v___x_413_ = lean_usize_of_nat(v___x_405_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_403_, v___x_412_, v___x_413_, v___x_407_);
v___y_394_ = v___x_414_;
goto v___jp_393_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 0);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_382_);
v___x_388_ = v_reuseFailAlloc_392_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_388_);
v___x_390_ = v___x_316_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
v___jp_393_:
{
if (lean_obj_tag(v___y_394_) == 0)
{
lean_dec_ref(v___y_394_);
goto v___jp_386_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_del_object(v___x_384_);
lean_dec(v_a_382_);
lean_del_object(v___x_316_);
v_a_395_ = lean_ctor_get(v___y_394_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___y_394_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___y_394_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___y_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_381_);
lean_del_object(v___x_316_);
goto v___jp_338_;
}
}
}
v___jp_338_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_339_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__1));
v___x_340_ = lean_string_append(v___x_339_, v___x_337_);
lean_dec_ref(v___x_337_);
v___x_341_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__2));
v___x_342_ = lean_string_append(v___x_340_, v___x_341_);
v___x_343_ = lean_string_append(v___x_342_, v_stdout_330_);
lean_dec_ref(v_stdout_330_);
v___x_344_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
v___x_346_ = lean_string_append(v___x_345_, v_stderr_331_);
lean_dec_ref(v_stderr_331_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 3);
lean_ctor_set(v___x_311_, 0, v___x_346_);
v___x_348_ = v___x_311_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_348_);
v___x_350_ = v___x_326_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_del_object(v___x_316_);
lean_del_object(v___x_311_);
v_a_417_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_323_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_323_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_del_object(v___x_311_);
lean_dec(v_val_309_);
lean_dec_ref(v_handleStderr_305_);
lean_dec_ref(v_header_304_);
v_a_426_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_313_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_313_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v___x_308_);
lean_dec_ref(v_handleStderr_305_);
lean_dec_ref(v_header_304_);
v___x_435_ = lean_box(1);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object* v_m_437_, lean_object* v_header_438_, lean_object* v_handleStderr_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Server_FileWorker_setupFile(v_m_437_, v_header_438_, v_handleStderr_439_);
lean_dec_ref(v_m_437_);
return v_res_441_;
}
}
lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_LakePath(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
