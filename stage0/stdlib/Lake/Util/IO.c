// Lean compiler output
// Module: Lake.Util.IO
// Imports: public import Init.System.IO
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
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_realpath(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
lean_object* lean_io_symlink_metadata(lean_object*);
uint8_t l_IO_FS_instBEqFileType_beq(uint8_t, uint8_t);
lean_object* lean_io_read_dir(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_io_remove_dir(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFileIfNew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFileIfNew___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBinFileIfNew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBinFileIfNew___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyDirAll___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolvePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_resolvePath___closed__0 = (const lean_object*)&l_Lake_resolvePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_resolvePath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object* v_path_1_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_System_FilePath_parent(v_path_1_);
if (lean_obj_tag(v___x_3_) == 1)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
v_val_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v___x_3_, 1);
v___x_5_ = l_IO_FS_createDirAll(v_val_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v___x_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT void l_Lake_createParentDirs_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_1_ = stack[0].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lake_createParentDirs(v_path_1_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_createParentDirs___boxed(lean_object* v_path_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lake_createParentDirs(v_path_9_);
return v_res_11_;
}
}
lean_object* l_Lake_removeFileIfExists(lean_object* v_path_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_io_remove_file(v_path_12_);
if (lean_obj_tag(v___x_14_) == 0)
{
return v___x_14_;
}
else
{
lean_object* v_a_15_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
if (lean_obj_tag(v_a_15_) == 11)
{
lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_14_, 0);
lean_dec(v_unused_24_);
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
else
{
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_19_ = lean_box(0);
if (v_isShared_18_ == 0)
{
lean_ctor_set_tag(v___x_17_, 0);
lean_ctor_set(v___x_17_, 0, v___x_19_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
else
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT void l_Lake_removeFileIfExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_12_ = stack[0].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lake_removeFileIfExists(v_path_12_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists___boxed(lean_object* v_path_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_removeFileIfExists(v_path_26_);
lean_dec_ref(v_path_26_);
return v_res_28_;
}
}
lean_object* l_Lake_writeFileIfNew(lean_object* v_path_29_, lean_object* v_content_30_){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; 
v___x_32_ = 2;
v___x_33_ = lean_io_prim_handle_mk(v_path_29_, v___x_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v___x_35_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
lean_dec_ref_known(v___x_33_, 1);
v___x_35_ = lean_io_prim_handle_put_str(v_a_34_, v_content_30_);
lean_dec(v_a_34_);
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_47_; 
v_a_36_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_47_ == 0)
{
v___x_38_ = v___x_33_;
v_isShared_39_ = v_isSharedCheck_47_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_33_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_47_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
if (lean_obj_tag(v_a_36_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_42_; 
lean_dec_ref_known(v_a_36_, 2);
v___x_40_ = lean_box(0);
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 0);
lean_ctor_set(v___x_38_, 0, v___x_40_);
v___x_42_ = v___x_38_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
else
{
lean_object* v___x_45_; 
if (v_isShared_39_ == 0)
{
v___x_45_ = v___x_38_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_36_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_writeFileIfNew_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_29_ = stack[0].m_obj;
lean_object* v_content_30_ = stack[1].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lake_writeFileIfNew(v_path_29_, v_content_30_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lake_writeFileIfNew___boxed(lean_object* v_path_49_, lean_object* v_content_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lake_writeFileIfNew(v_path_49_, v_content_50_);
lean_dec_ref(v_content_50_);
lean_dec_ref(v_path_49_);
return v_res_52_;
}
}
lean_object* l_Lake_writeBinFileIfNew(lean_object* v_path_53_, lean_object* v_content_54_){
_start:
{
uint8_t v___x_56_; lean_object* v___x_57_; 
v___x_56_ = 2;
v___x_57_ = lean_io_prim_handle_mk(v_path_53_, v___x_56_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_57_, 1);
v___x_59_ = lean_io_prim_handle_write(v_a_58_, v_content_54_);
lean_dec(v_a_58_);
return v___x_59_;
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_71_; 
v_a_60_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_71_ == 0)
{
v___x_62_ = v___x_57_;
v_isShared_63_ = v_isSharedCheck_71_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_57_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_71_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
if (lean_obj_tag(v_a_60_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_66_; 
lean_dec_ref_known(v_a_60_, 2);
v___x_64_ = lean_box(0);
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 0);
lean_ctor_set(v___x_62_, 0, v___x_64_);
v___x_66_ = v___x_62_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_object* v___x_69_; 
if (v_isShared_63_ == 0)
{
v___x_69_ = v___x_62_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_60_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_writeBinFileIfNew_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_53_ = stack[0].m_obj;
lean_object* v_content_54_ = stack[1].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lake_writeBinFileIfNew(v_path_53_, v_content_54_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lake_writeBinFileIfNew___boxed(lean_object* v_path_73_, lean_object* v_content_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lake_writeBinFileIfNew(v_path_73_, v_content_74_);
lean_dec_ref(v_content_74_);
lean_dec_ref(v_path_73_);
return v_res_76_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object* v_as_77_, size_t v_sz_78_, size_t v_i_79_, lean_object* v_b_80_){
_start:
{
lean_object* v_a_83_; uint8_t v___x_87_; 
v___x_87_ = lean_usize_dec_lt(v_i_79_, v_sz_78_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v_b_80_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; lean_object* v_a_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_box(0);
v_a_90_ = lean_array_uget_borrowed(v_as_77_, v_i_79_);
lean_inc(v_a_90_);
v___x_91_ = l_IO_FS_DirEntry_path(v_a_90_);
v___x_92_ = lean_io_symlink_metadata(v___x_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; uint8_t v_type_94_; uint8_t v___x_95_; uint8_t v___x_96_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_92_, 1);
v_type_94_ = lean_ctor_get_uint8(v_a_93_, sizeof(void*)*2 + 16);
lean_dec(v_a_93_);
v___x_95_ = 0;
v___x_96_ = l_IO_FS_instBEqFileType_beq(v_type_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = l_Lake_removeFileIfExists(v___x_91_);
lean_dec_ref(v___x_91_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_dec_ref_known(v___x_97_, 1);
v_a_83_ = v___x_89_;
goto v___jp_82_;
}
else
{
return v___x_97_;
}
}
else
{
lean_object* v___x_98_; 
v___x_98_ = l_Lake_removeDirAllIfExists(v___x_91_);
lean_dec_ref(v___x_91_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_dec_ref_known(v___x_98_, 1);
v_a_83_ = v___x_89_;
goto v___jp_82_;
}
else
{
return v___x_98_;
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec_ref(v___x_91_);
v_a_99_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_92_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_92_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
if (lean_obj_tag(v_a_99_) == 11)
{
lean_dec_ref_known(v_a_99_, 2);
lean_del_object(v___x_101_);
v_a_83_ = v___x_89_;
goto v___jp_82_;
}
else
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
v___jp_82_:
{
size_t v___x_84_; size_t v___x_85_; 
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_add(v_i_79_, v___x_84_);
v_i_79_ = v___x_85_;
v_b_80_ = v_a_83_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_77_ = stack[0].m_obj;
size_t v_sz_78_ = stack[1].m_num;
size_t v_i_79_ = stack[2].m_num;
lean_object* v_b_80_ = stack[3].m_obj;
lean_object* v_res_107_;
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_as_77_, v_sz_78_, v_i_79_, v_b_80_);
stack->m_obj
 = v_res_107_;
}
lean_object* l_Lake_removeDirAllIfExists(lean_object* v_path_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_io_read_dir(v_path_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_112_; size_t v_sz_113_; size_t v___x_114_; lean_object* v___x_115_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = lean_box(0);
v_sz_113_ = lean_array_size(v_a_111_);
v___x_114_ = ((size_t)0ULL);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_a_111_, v_sz_113_, v___x_114_, v___x_112_);
lean_dec(v_a_111_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = lean_io_remove_dir(v_path_108_);
if (lean_obj_tag(v___x_116_) == 0)
{
return v___x_116_;
}
else
{
lean_object* v_a_117_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
if (lean_obj_tag(v_a_117_) == 11)
{
lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; 
v_unused_125_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_125_);
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 0);
lean_ctor_set(v___x_119_, 0, v___x_112_);
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_112_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
return v___x_116_;
}
}
}
else
{
return v___x_115_;
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_137_; 
v_a_126_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_137_ == 0)
{
v___x_128_ = v___x_110_;
v_isShared_129_ = v_isSharedCheck_137_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_110_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_137_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
if (lean_obj_tag(v_a_126_) == 11)
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_dec_ref_known(v_a_126_, 2);
v___x_130_ = lean_box(0);
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 0);
lean_ctor_set(v___x_128_, 0, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
else
{
lean_object* v___x_135_; 
if (v_isShared_129_ == 0)
{
v___x_135_ = v___x_128_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_126_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_removeDirAllIfExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_108_ = stack[0].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lake_removeDirAllIfExists(v_path_108_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object* v_path_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lake_removeDirAllIfExists(v_path_139_);
lean_dec_ref(v_path_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object* v_as_142_, lean_object* v_sz_143_, lean_object* v_i_144_, lean_object* v_b_145_, lean_object* v___y_146_){
_start:
{
size_t v_sz_boxed_147_; size_t v_i_boxed_148_; lean_object* v_res_149_; 
v_sz_boxed_147_ = lean_unbox_usize(v_sz_143_);
lean_dec(v_sz_143_);
v_i_boxed_148_ = lean_unbox_usize(v_i_144_);
lean_dec(v_i_144_);
v_res_149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_as_142_, v_sz_boxed_147_, v_i_boxed_148_, v_b_145_);
lean_dec_ref(v_as_142_);
return v_res_149_;
}
}
lean_object* l_Lake_copyFile(lean_object* v_src_150_, lean_object* v_dst_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_IO_FS_readBinFile(v_src_150_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = l_IO_FS_writeBinFile(v_dst_151_, v_a_154_);
lean_dec(v_a_154_);
return v___x_155_;
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_156_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_153_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_153_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_copyFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_150_ = stack[0].m_obj;
lean_object* v_dst_151_ = stack[1].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lake_copyFile(v_src_150_, v_dst_151_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object* v_src_165_, lean_object* v_dst_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lake_copyFile(v_src_165_, v_dst_166_);
lean_dec_ref(v_dst_166_);
lean_dec_ref(v_src_165_);
return v_res_168_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(lean_object* v_src_169_, lean_object* v_dst_170_, lean_object* v_as_171_, size_t v_sz_172_, size_t v_i_173_, lean_object* v_b_174_){
_start:
{
lean_object* v_a_177_; uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_173_, v_sz_172_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v_dst_170_);
lean_dec_ref(v_src_169_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_b_174_);
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v_fileName_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_a_183_ = lean_array_uget_borrowed(v_as_171_, v_i_173_);
v_fileName_184_ = lean_ctor_get(v_a_183_, 1);
v___x_185_ = lean_box(0);
lean_inc_ref_n(v_fileName_184_, 2);
lean_inc_ref(v_src_169_);
v___x_186_ = l_System_FilePath_join(v_src_169_, v_fileName_184_);
lean_inc_ref(v_dst_170_);
v___x_187_ = l_System_FilePath_join(v_dst_170_, v_fileName_184_);
v___x_188_ = l_System_FilePath_isDir(v___x_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = l_Lake_copyFile(v___x_186_, v___x_187_);
lean_dec_ref(v___x_187_);
lean_dec_ref(v___x_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_dec_ref_known(v___x_189_, 1);
v_a_177_ = v___x_185_;
goto v___jp_176_;
}
else
{
lean_dec_ref(v_dst_170_);
lean_dec_ref(v_src_169_);
return v___x_189_;
}
}
else
{
lean_object* v___x_190_; 
v___x_190_ = l_Lake_copyDirAll(v___x_186_, v___x_187_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_dec_ref_known(v___x_190_, 1);
v_a_177_ = v___x_185_;
goto v___jp_176_;
}
else
{
lean_dec_ref(v_dst_170_);
lean_dec_ref(v_src_169_);
return v___x_190_;
}
}
}
v___jp_176_:
{
size_t v___x_178_; size_t v___x_179_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_173_, v___x_178_);
v_i_173_ = v___x_179_;
v_b_174_ = v_a_177_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_169_ = stack[0].m_obj;
lean_object* v_dst_170_ = stack[1].m_obj;
lean_object* v_as_171_ = stack[2].m_obj;
size_t v_sz_172_ = stack[3].m_num;
size_t v_i_173_ = stack[4].m_num;
lean_object* v_b_174_ = stack[5].m_obj;
lean_object* v_res_191_;
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_169_, v_dst_170_, v_as_171_, v_sz_172_, v_i_173_, v_b_174_);
stack->m_obj
 = v_res_191_;
}
lean_object* l_Lake_copyDirAll(lean_object* v_src_192_, lean_object* v_dst_193_){
_start:
{
lean_object* v___x_195_; 
lean_inc_ref(v_dst_193_);
v___x_195_ = l_IO_FS_createDirAll(v_dst_193_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v___x_196_; 
lean_dec_ref_known(v___x_195_, 1);
v___x_196_ = lean_io_read_dir(v_src_192_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_198_; size_t v_sz_199_; size_t v___x_200_; lean_object* v___x_201_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_198_ = lean_box(0);
v_sz_199_ = lean_array_size(v_a_197_);
v___x_200_ = ((size_t)0ULL);
v___x_201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_192_, v_dst_193_, v_a_197_, v_sz_199_, v___x_200_, v___x_198_);
lean_dec(v_a_197_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v___x_201_, 0);
lean_dec(v_unused_209_);
v___x_203_ = v___x_201_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_dec(v___x_201_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_198_);
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_198_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
return v___x_201_;
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_dst_193_);
lean_dec_ref(v_src_192_);
v_a_210_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_196_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_196_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_dec_ref(v_dst_193_);
lean_dec_ref(v_src_192_);
return v___x_195_;
}
}
}
LEAN_EXPORT void l_Lake_copyDirAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_src_192_ = stack[0].m_obj;
lean_object* v_dst_193_ = stack[1].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lake_copyDirAll(v_src_192_, v_dst_193_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lake_copyDirAll___boxed(lean_object* v_src_219_, lean_object* v_dst_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lake_copyDirAll(v_src_219_, v_dst_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0___boxed(lean_object* v_src_223_, lean_object* v_dst_224_, lean_object* v_as_225_, lean_object* v_sz_226_, lean_object* v_i_227_, lean_object* v_b_228_, lean_object* v___y_229_){
_start:
{
size_t v_sz_boxed_230_; size_t v_i_boxed_231_; lean_object* v_res_232_; 
v_sz_boxed_230_ = lean_unbox_usize(v_sz_226_);
lean_dec(v_sz_226_);
v_i_boxed_231_ = lean_unbox_usize(v_i_227_);
lean_dec(v_i_227_);
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_223_, v_dst_224_, v_as_225_, v_sz_boxed_230_, v_i_boxed_231_, v_b_228_);
lean_dec_ref(v_as_225_);
return v_res_232_;
}
}
lean_object* l_Lake_resolvePath(lean_object* v_path_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_io_realpath(v_path_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; uint8_t v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = l_System_FilePath_pathExists(v_a_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v_a_237_);
v___x_239_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = l_System_FilePath_normalize(v_a_237_);
return v___x_240_;
}
}
else
{
lean_object* v___x_241_; 
lean_dec_ref_known(v___x_236_, 1);
v___x_241_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_241_;
}
}
}
LEAN_EXPORT void l_Lake_resolvePath_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_234_ = stack[0].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lake_resolvePath(v_path_234_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object* v_path_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_resolvePath(v_path_243_);
return v_res_245_;
}
}
lean_object* l_Lake_resolvePath_x3f(lean_object* v_path_246_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_248_ = l_Lake_resolvePath(v_path_246_);
v___x_249_ = lean_string_utf8_byte_size(v___x_248_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_nat_dec_eq(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_248_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
lean_dec_ref(v___x_248_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
}
LEAN_EXPORT void l_Lake_resolvePath_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_246_ = stack[0].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_Lake_resolvePath_x3f(v_path_246_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object* v_path_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lake_resolvePath_x3f(v_path_255_);
return v_res_257_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_IO(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_IO(builtin);
}
#ifdef __cplusplus
}
#endif
