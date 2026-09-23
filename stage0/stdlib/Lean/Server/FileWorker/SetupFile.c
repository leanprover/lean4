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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object* v_x_210_){
_start:
{
switch(lean_obj_tag(v_x_210_))
{
case 0:
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(0u);
return v___x_211_;
}
case 1:
{
lean_object* v___x_212_; 
v___x_212_ = lean_unsigned_to_nat(1u);
return v___x_212_;
}
case 2:
{
lean_object* v___x_213_; 
v___x_213_ = lean_unsigned_to_nat(2u);
return v___x_213_;
}
default: 
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(3u);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(v_x_215_);
lean_dec(v_x_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(lean_object* v_t_217_, lean_object* v_k_218_){
_start:
{
switch(lean_obj_tag(v_t_217_))
{
case 0:
{
lean_object* v_setup_219_; lean_object* v___x_220_; 
v_setup_219_ = lean_ctor_get(v_t_217_, 0);
lean_inc_ref(v_setup_219_);
lean_dec_ref_known(v_t_217_, 1);
v___x_220_ = lean_apply_1(v_k_218_, v_setup_219_);
return v___x_220_;
}
case 3:
{
lean_object* v_msg_221_; lean_object* v___x_222_; 
v_msg_221_ = lean_ctor_get(v_t_217_, 0);
lean_inc_ref(v_msg_221_);
lean_dec_ref_known(v_t_217_, 1);
v___x_222_ = lean_apply_1(v_k_218_, v_msg_221_);
return v___x_222_;
}
default: 
{
lean_dec(v_t_217_);
return v_k_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_225_, v_k_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(lean_object* v_motive_229_, lean_object* v_ctorIdx_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_k_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(v_motive_229_, v_ctorIdx_230_, v_t_231_, v_h_232_, v_k_233_);
lean_dec(v_ctorIdx_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(lean_object* v_t_235_, lean_object* v_success_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_235_, v_success_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_success_elim(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_success_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_239_, v_success_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(lean_object* v_t_243_, lean_object* v_noLakefile_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_243_, v_noLakefile_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(lean_object* v_motive_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_noLakefile_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_247_, v_noLakefile_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(lean_object* v_t_251_, lean_object* v_importsOutOfDate_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_251_, v_importsOutOfDate_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(lean_object* v_motive_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_importsOutOfDate_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_255_, v_importsOutOfDate_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(lean_object* v_t_259_, lean_object* v_error_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_259_, v_error_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_error_elim(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_error_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_263_, v_error_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(lean_object* v_as_267_, size_t v_i_268_, size_t v_stop_269_, lean_object* v_b_270_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_eq(v_i_268_, v_stop_269_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_array_uget_borrowed(v_as_267_, v_i_268_);
lean_inc(v___x_273_);
v___x_274_ = lean_load_dynlib(v___x_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; size_t v___x_276_; size_t v___x_277_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_274_, 1);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_268_, v___x_276_);
v_i_268_ = v___x_277_;
v_b_270_ = v_a_275_;
goto _start;
}
else
{
return v___x_274_;
}
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_b_270_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* v_as_280_, lean_object* v_i_281_, lean_object* v_stop_282_, lean_object* v_b_283_, lean_object* v___y_284_){
_start:
{
size_t v_i_boxed_285_; size_t v_stop_boxed_286_; lean_object* v_res_287_; 
v_i_boxed_285_ = lean_unbox_usize(v_i_281_);
lean_dec(v_i_281_);
v_stop_boxed_286_ = lean_unbox_usize(v_stop_282_);
lean_dec(v_stop_282_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_280_, v_i_boxed_285_, v_stop_boxed_286_, v_b_283_);
lean_dec_ref(v_as_280_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* v_m_294_, lean_object* v_header_295_, lean_object* v_handleStderr_296_){
_start:
{
lean_object* v_uri_298_; lean_object* v___x_299_; 
v_uri_298_ = lean_ctor_get(v_m_294_, 0);
v___x_299_ = l_System_Uri_fileUriToPath_x3f(v_uri_298_);
if (lean_obj_tag(v___x_299_) == 1)
{
lean_object* v_val_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_425_; 
v_val_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_425_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_425_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_val_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_425_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_determineLakePath();
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_416_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_416_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_416_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_416_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
uint8_t v___x_309_; 
v___x_309_ = l_System_FilePath_pathExists(v_a_305_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v_a_305_);
lean_del_object(v___x_302_);
lean_dec(v_val_300_);
lean_dec_ref(v_handleStderr_296_);
lean_dec_ref(v_header_295_);
v___x_310_ = lean_box(1);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_310_);
v___x_312_ = v___x_307_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Server_FileWorker_runLakeSetupFile(v_m_294_, v_a_305_, v_val_300_, v_header_295_, v_handleStderr_296_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_407_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_407_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_407_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_407_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_spawnArgs_319_; uint32_t v_exitCode_320_; lean_object* v_stdout_321_; lean_object* v_stderr_322_; lean_object* v_cmd_323_; lean_object* v_args_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint32_t v___x_344_; uint8_t v___x_345_; 
v_spawnArgs_319_ = lean_ctor_get(v_a_315_, 0);
lean_inc_ref(v_spawnArgs_319_);
v_exitCode_320_ = lean_ctor_get_uint32(v_a_315_, sizeof(void*)*3);
v_stdout_321_ = lean_ctor_get(v_a_315_, 1);
lean_inc_ref(v_stdout_321_);
v_stderr_322_ = lean_ctor_get(v_a_315_, 2);
lean_inc_ref(v_stderr_322_);
lean_dec(v_a_315_);
v_cmd_323_ = lean_ctor_get(v_spawnArgs_319_, 1);
lean_inc_ref(v_cmd_323_);
v_args_324_ = lean_ctor_get(v_spawnArgs_319_, 2);
lean_inc_ref(v_args_324_);
lean_dec_ref(v_spawnArgs_319_);
v___x_325_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__0));
v___x_326_ = lean_array_to_list(v_args_324_);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v_cmd_323_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_String_intercalate(v___x_325_, v___x_327_);
v___x_344_ = 0;
v___x_345_ = lean_uint32_dec_eq(v_exitCode_320_, v___x_344_);
if (v___x_345_ == 0)
{
uint32_t v___x_346_; uint8_t v___x_347_; 
lean_del_object(v___x_317_);
lean_del_object(v___x_302_);
v___x_346_ = 2;
v___x_347_ = lean_uint32_dec_eq(v_exitCode_320_, v___x_346_);
if (v___x_347_ == 0)
{
uint32_t v___x_348_; uint8_t v___x_349_; 
v___x_348_ = 3;
v___x_349_ = lean_uint32_dec_eq(v_exitCode_320_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_350_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__4));
v___x_351_ = lean_string_append(v___x_350_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_352_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__5));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___x_354_ = lean_string_append(v___x_353_, v_stdout_321_);
lean_dec_ref(v_stdout_321_);
v___x_355_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
v___x_357_ = lean_string_append(v___x_356_, v_stderr_322_);
lean_dec_ref(v_stderr_322_);
v___x_358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_358_);
v___x_360_ = v___x_307_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_dec_ref(v___x_328_);
lean_dec_ref(v_stderr_322_);
lean_dec_ref(v_stdout_321_);
v___x_362_ = lean_box(2);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_362_);
v___x_364_ = v___x_307_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_dec_ref(v___x_328_);
lean_dec_ref(v_stderr_322_);
lean_dec_ref(v_stdout_321_);
v___x_366_ = lean_box(1);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_366_);
v___x_368_ = v___x_307_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v___x_370_; 
lean_inc_ref(v_stdout_321_);
v___x_370_ = l_Lean_Json_parse(v_stdout_321_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_dec_ref_known(v___x_370_, 1);
lean_del_object(v___x_307_);
goto v___jp_329_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_372_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_371_);
if (lean_obj_tag(v___x_372_) == 1)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v___x_328_);
lean_dec_ref(v_stderr_322_);
lean_dec_ref(v_stdout_321_);
lean_del_object(v___x_317_);
lean_del_object(v___x_302_);
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_406_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_406_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_406_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___y_385_; lean_object* v_dynlibs_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_dynlibs_394_ = lean_ctor_get(v_a_373_, 4);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_array_get_size(v_dynlibs_394_);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
goto v___jp_377_;
}
else
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_nat_dec_le(v___x_396_, v___x_396_);
if (v___x_399_ == 0)
{
if (v___x_397_ == 0)
{
goto v___jp_377_;
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_396_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_394_, v___x_400_, v___x_401_, v___x_398_);
v___y_385_ = v___x_402_;
goto v___jp_384_;
}
}
else
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((size_t)0ULL);
v___x_404_ = lean_usize_of_nat(v___x_396_);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_394_, v___x_403_, v___x_404_, v___x_398_);
v___y_385_ = v___x_405_;
goto v___jp_384_;
}
}
v___jp_377_:
{
lean_object* v___x_379_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 0);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_373_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_379_);
v___x_381_ = v___x_307_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
v___jp_384_:
{
if (lean_obj_tag(v___y_385_) == 0)
{
lean_dec_ref_known(v___y_385_, 1);
goto v___jp_377_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_del_object(v___x_375_);
lean_dec(v_a_373_);
lean_del_object(v___x_307_);
v_a_386_ = lean_ctor_get(v___y_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___y_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___y_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___y_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_372_);
lean_del_object(v___x_307_);
goto v___jp_329_;
}
}
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_330_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__1));
v___x_331_ = lean_string_append(v___x_330_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_332_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__2));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_string_append(v___x_333_, v_stdout_321_);
lean_dec_ref(v_stdout_321_);
v___x_335_ = ((lean_object*)(l_Lean_Server_FileWorker_setupFile___closed__3));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
v___x_337_ = lean_string_append(v___x_336_, v_stderr_322_);
lean_dec_ref(v_stderr_322_);
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 3);
lean_ctor_set(v___x_302_, 0, v___x_337_);
v___x_339_ = v___x_302_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_339_);
v___x_341_ = v___x_317_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_del_object(v___x_307_);
lean_del_object(v___x_302_);
v_a_408_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_314_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_314_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_del_object(v___x_302_);
lean_dec(v_val_300_);
lean_dec_ref(v_handleStderr_296_);
lean_dec_ref(v_header_295_);
v_a_417_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_304_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_304_);
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
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v___x_299_);
lean_dec_ref(v_handleStderr_296_);
lean_dec_ref(v_header_295_);
v___x_426_ = lean_box(1);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile___boxed(lean_object* v_m_428_, lean_object* v_header_429_, lean_object* v_handleStderr_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Server_FileWorker_setupFile(v_m_428_, v_header_429_, v_handleStderr_430_);
lean_dec_ref(v_m_428_);
return v_res_432_;
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
