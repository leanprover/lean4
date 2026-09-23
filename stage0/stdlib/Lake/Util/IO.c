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
LEAN_EXPORT lean_object* l_Lake_createParentDirs(lean_object* v_path_1_){
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
LEAN_EXPORT lean_object* l_Lake_createParentDirs___boxed(lean_object* v_path_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_createParentDirs(v_path_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists(lean_object* v_path_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_io_remove_file(v_path_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
return v___x_13_;
}
else
{
lean_object* v_a_14_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
if (lean_obj_tag(v_a_14_) == 11)
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
lean_dec_ref_known(v_a_14_, 2);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; 
v_unused_23_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_23_);
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
if (v_isShared_17_ == 0)
{
lean_ctor_set_tag(v___x_16_, 0);
lean_ctor_set(v___x_16_, 0, v___x_18_);
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
lean_dec(v_a_14_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists___boxed(lean_object* v_path_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_removeFileIfExists(v_path_24_);
lean_dec_ref(v_path_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileIfNew(lean_object* v_path_27_, lean_object* v_content_28_){
_start:
{
uint8_t v___x_30_; lean_object* v___x_31_; 
v___x_30_ = 2;
v___x_31_ = lean_io_prim_handle_mk(v_path_27_, v___x_30_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_33_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_31_, 1);
v___x_33_ = lean_io_prim_handle_put_str(v_a_32_, v_content_28_);
lean_dec(v_a_32_);
return v___x_33_;
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_45_; 
v_a_34_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_45_ == 0)
{
v___x_36_ = v___x_31_;
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_31_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
if (lean_obj_tag(v_a_34_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_dec_ref_known(v_a_34_, 2);
v___x_38_ = lean_box(0);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 0);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
else
{
lean_object* v___x_43_; 
if (v_isShared_37_ == 0)
{
v___x_43_ = v___x_36_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_34_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileIfNew___boxed(lean_object* v_path_46_, lean_object* v_content_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lake_writeFileIfNew(v_path_46_, v_content_47_);
lean_dec_ref(v_content_47_);
lean_dec_ref(v_path_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBinFileIfNew(lean_object* v_path_50_, lean_object* v_content_51_){
_start:
{
uint8_t v___x_53_; lean_object* v___x_54_; 
v___x_53_ = 2;
v___x_54_ = lean_io_prim_handle_mk(v_path_50_, v___x_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_56_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_a_55_);
lean_dec_ref_known(v___x_54_, 1);
v___x_56_ = lean_io_prim_handle_write(v_a_55_, v_content_51_);
lean_dec(v_a_55_);
return v___x_56_;
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_68_; 
v_a_57_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_68_ == 0)
{
v___x_59_ = v___x_54_;
v_isShared_60_ = v_isSharedCheck_68_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_54_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_68_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
if (lean_obj_tag(v_a_57_) == 0)
{
lean_object* v___x_61_; lean_object* v___x_63_; 
lean_dec_ref_known(v_a_57_, 2);
v___x_61_ = lean_box(0);
if (v_isShared_60_ == 0)
{
lean_ctor_set_tag(v___x_59_, 0);
lean_ctor_set(v___x_59_, 0, v___x_61_);
v___x_63_ = v___x_59_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
else
{
lean_object* v___x_66_; 
if (v_isShared_60_ == 0)
{
v___x_66_ = v___x_59_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_57_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeBinFileIfNew___boxed(lean_object* v_path_69_, lean_object* v_content_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lake_writeBinFileIfNew(v_path_69_, v_content_70_);
lean_dec_ref(v_content_70_);
lean_dec_ref(v_path_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object* v_as_73_, size_t v_sz_74_, size_t v_i_75_, lean_object* v_b_76_){
_start:
{
lean_object* v_a_79_; uint8_t v___x_83_; 
v___x_83_ = lean_usize_dec_lt(v_i_75_, v_sz_74_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_b_76_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v_a_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_box(0);
v_a_86_ = lean_array_uget_borrowed(v_as_73_, v_i_75_);
lean_inc(v_a_86_);
v___x_87_ = l_IO_FS_DirEntry_path(v_a_86_);
v___x_88_ = lean_io_symlink_metadata(v___x_87_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; uint8_t v_type_90_; uint8_t v___x_91_; uint8_t v___x_92_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
v_type_90_ = lean_ctor_get_uint8(v_a_89_, sizeof(void*)*2 + 16);
lean_dec(v_a_89_);
v___x_91_ = 0;
v___x_92_ = l_IO_FS_instBEqFileType_beq(v_type_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
v___x_93_ = l_Lake_removeFileIfExists(v___x_87_);
lean_dec_ref(v___x_87_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_dec_ref_known(v___x_93_, 1);
v_a_79_ = v___x_85_;
goto v___jp_78_;
}
else
{
return v___x_93_;
}
}
else
{
lean_object* v___x_94_; 
v___x_94_ = l_Lake_removeDirAllIfExists(v___x_87_);
lean_dec_ref(v___x_87_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_dec_ref_known(v___x_94_, 1);
v_a_79_ = v___x_85_;
goto v___jp_78_;
}
else
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v___x_87_);
v_a_95_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_88_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_88_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
if (lean_obj_tag(v_a_95_) == 11)
{
lean_dec_ref_known(v_a_95_, 2);
lean_del_object(v___x_97_);
v_a_79_ = v___x_85_;
goto v___jp_78_;
}
else
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
v___jp_78_:
{
size_t v___x_80_; size_t v___x_81_; 
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_add(v_i_75_, v___x_80_);
v_i_75_ = v___x_81_;
v_b_76_ = v_a_79_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object* v_path_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_io_read_dir(v_path_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; size_t v_sz_108_; size_t v___x_109_; lean_object* v___x_110_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = lean_box(0);
v_sz_108_ = lean_array_size(v_a_106_);
v___x_109_ = ((size_t)0ULL);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_a_106_, v_sz_108_, v___x_109_, v___x_107_);
lean_dec(v_a_106_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
lean_dec_ref_known(v___x_110_, 1);
v___x_111_ = lean_io_remove_dir(v_path_103_);
if (lean_obj_tag(v___x_111_) == 0)
{
return v___x_111_;
}
else
{
lean_object* v_a_112_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
if (lean_obj_tag(v_a_112_) == 11)
{
lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref_known(v_a_112_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v___x_111_, 0);
lean_dec(v_unused_120_);
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 0);
lean_ctor_set(v___x_114_, 0, v___x_107_);
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_107_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_dec(v_a_112_);
return v___x_111_;
}
}
}
else
{
return v___x_110_;
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
v_a_121_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v___x_105_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_105_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
if (lean_obj_tag(v_a_121_) == 11)
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_dec_ref_known(v_a_121_, 2);
v___x_125_ = lean_box(0);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 0);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
lean_object* v___x_130_; 
if (v_isShared_124_ == 0)
{
v___x_130_ = v___x_123_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_121_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object* v_path_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lake_removeDirAllIfExists(v_path_133_);
lean_dec_ref(v_path_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object* v_as_136_, lean_object* v_sz_137_, lean_object* v_i_138_, lean_object* v_b_139_, lean_object* v___y_140_){
_start:
{
size_t v_sz_boxed_141_; size_t v_i_boxed_142_; lean_object* v_res_143_; 
v_sz_boxed_141_ = lean_unbox_usize(v_sz_137_);
lean_dec(v_sz_137_);
v_i_boxed_142_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_as_136_, v_sz_boxed_141_, v_i_boxed_142_, v_b_139_);
lean_dec_ref(v_as_136_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object* v_src_144_, lean_object* v_dst_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_IO_FS_readBinFile(v_src_144_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = l_IO_FS_writeBinFile(v_dst_145_, v_a_148_);
lean_dec(v_a_148_);
return v___x_149_;
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_147_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_147_);
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
}
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object* v_src_158_, lean_object* v_dst_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lake_copyFile(v_src_158_, v_dst_159_);
lean_dec_ref(v_dst_159_);
lean_dec_ref(v_src_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(lean_object* v_src_162_, lean_object* v_dst_163_, lean_object* v_as_164_, size_t v_sz_165_, size_t v_i_166_, lean_object* v_b_167_){
_start:
{
lean_object* v_a_170_; uint8_t v___x_174_; 
v___x_174_ = lean_usize_dec_lt(v_i_166_, v_sz_165_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec_ref(v_dst_163_);
lean_dec_ref(v_src_162_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v_b_167_);
return v___x_175_;
}
else
{
lean_object* v_a_176_; lean_object* v_fileName_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_a_176_ = lean_array_uget_borrowed(v_as_164_, v_i_166_);
v_fileName_177_ = lean_ctor_get(v_a_176_, 1);
v___x_178_ = lean_box(0);
lean_inc_ref_n(v_fileName_177_, 2);
lean_inc_ref(v_src_162_);
v___x_179_ = l_System_FilePath_join(v_src_162_, v_fileName_177_);
lean_inc_ref(v_dst_163_);
v___x_180_ = l_System_FilePath_join(v_dst_163_, v_fileName_177_);
v___x_181_ = l_System_FilePath_isDir(v___x_179_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = l_Lake_copyFile(v___x_179_, v___x_180_);
lean_dec_ref(v___x_180_);
lean_dec_ref(v___x_179_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_dec_ref_known(v___x_182_, 1);
v_a_170_ = v___x_178_;
goto v___jp_169_;
}
else
{
lean_dec_ref(v_dst_163_);
lean_dec_ref(v_src_162_);
return v___x_182_;
}
}
else
{
lean_object* v___x_183_; 
v___x_183_ = l_Lake_copyDirAll(v___x_179_, v___x_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_dec_ref_known(v___x_183_, 1);
v_a_170_ = v___x_178_;
goto v___jp_169_;
}
else
{
lean_dec_ref(v_dst_163_);
lean_dec_ref(v_src_162_);
return v___x_183_;
}
}
}
v___jp_169_:
{
size_t v___x_171_; size_t v___x_172_; 
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_add(v_i_166_, v___x_171_);
v_i_166_ = v___x_172_;
v_b_167_ = v_a_170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyDirAll(lean_object* v_src_184_, lean_object* v_dst_185_){
_start:
{
lean_object* v___x_187_; 
lean_inc_ref(v_dst_185_);
v___x_187_ = l_IO_FS_createDirAll(v_dst_185_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_188_; 
lean_dec_ref_known(v___x_187_, 1);
v___x_188_ = lean_io_read_dir(v_src_184_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; size_t v_sz_191_; size_t v___x_192_; lean_object* v___x_193_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
v___x_190_ = lean_box(0);
v_sz_191_ = lean_array_size(v_a_189_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_184_, v_dst_185_, v_a_189_, v_sz_191_, v___x_192_, v___x_190_);
lean_dec(v_a_189_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v___x_193_, 0);
lean_dec(v_unused_201_);
v___x_195_ = v___x_193_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_dec(v___x_193_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_190_);
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_190_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
return v___x_193_;
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_dst_185_);
lean_dec_ref(v_src_184_);
v_a_202_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_188_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_188_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_dec_ref(v_dst_185_);
lean_dec_ref(v_src_184_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyDirAll___boxed(lean_object* v_src_210_, lean_object* v_dst_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_copyDirAll(v_src_210_, v_dst_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0___boxed(lean_object* v_src_214_, lean_object* v_dst_215_, lean_object* v_as_216_, lean_object* v_sz_217_, lean_object* v_i_218_, lean_object* v_b_219_, lean_object* v___y_220_){
_start:
{
size_t v_sz_boxed_221_; size_t v_i_boxed_222_; lean_object* v_res_223_; 
v_sz_boxed_221_ = lean_unbox_usize(v_sz_217_);
lean_dec(v_sz_217_);
v_i_boxed_222_ = lean_unbox_usize(v_i_218_);
lean_dec(v_i_218_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_214_, v_dst_215_, v_as_216_, v_sz_boxed_221_, v_i_boxed_222_, v_b_219_);
lean_dec_ref(v_as_216_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath(lean_object* v_path_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_io_realpath(v_path_225_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; uint8_t v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_System_FilePath_pathExists(v_a_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_dec(v_a_228_);
v___x_230_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_230_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = l_System_FilePath_normalize(v_a_228_);
return v___x_231_;
}
}
else
{
lean_object* v___x_232_; 
lean_dec_ref_known(v___x_227_, 1);
v___x_232_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object* v_path_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lake_resolvePath(v_path_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f(lean_object* v_path_236_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_238_ = l_Lake_resolvePath(v_path_236_);
v___x_239_ = lean_string_utf8_byte_size(v___x_238_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_238_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
lean_dec_ref(v___x_238_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object* v_path_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_resolvePath_x3f(v_path_244_);
return v_res_246_;
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
