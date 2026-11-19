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
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_io_rename_if_new(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*);
uint8_t lean_sarray_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Util_IO_0__Lake_publishFileIfNew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_IO_0__Lake_publishFileIfNew___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_writeBinFileAtomicIfNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "part.tmp"};
static const lean_object* l_Lake_writeBinFileAtomicIfNew___closed__0 = (const lean_object*)&l_Lake_writeBinFileAtomicIfNew___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_writeBinFileAtomicIfNew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBinFileAtomicIfNew___boxed(lean_object*, lean_object*, lean_object*);
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
if (lean_obj_tag(v_a_14_) == 11)
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
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
LEAN_EXPORT lean_object* l___private_Lake_Util_IO_0__Lake_publishFileIfNew(lean_object* v_src_73_, lean_object* v_dst_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_io_rename_if_new(v_src_73_, v_dst_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
return v___x_76_;
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_95_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_95_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_95_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_95_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = l_System_FilePath_pathExists(v_dst_74_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; 
if (v_isShared_80_ == 0)
{
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_77_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
lean_object* v___x_85_; 
lean_del_object(v___x_79_);
lean_dec(v_a_77_);
v___x_85_ = lean_io_remove_file(v_src_73_);
if (lean_obj_tag(v___x_85_) == 0)
{
return v___x_85_;
}
else
{
lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v___x_85_, 0);
lean_dec(v_unused_94_);
v___x_87_ = v___x_85_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_dec(v___x_85_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_box(0);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 0);
lean_ctor_set(v___x_87_, 0, v___x_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_IO_0__Lake_publishFileIfNew___boxed(lean_object* v_src_96_, lean_object* v_dst_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lake_Util_IO_0__Lake_publishFileIfNew(v_src_96_, v_dst_97_);
lean_dec_ref(v_dst_97_);
lean_dec_ref(v_src_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBinFileAtomicIfNew(lean_object* v_path_101_, lean_object* v_content_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_tmpFile_105_; lean_object* v___y_107_; uint8_t v___x_143_; lean_object* v___x_144_; 
v___x_104_ = ((lean_object*)(l_Lake_writeBinFileAtomicIfNew___closed__0));
lean_inc_ref(v_path_101_);
v_tmpFile_105_ = l_System_FilePath_addExtension(v_path_101_, v___x_104_);
v___x_143_ = 2;
v___x_144_ = lean_io_prim_handle_mk(v_tmpFile_105_, v___x_143_);
lean_dec_ref(v___x_144_);
goto v___jp_113_;
v___jp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_io_prim_handle_rewind(v___y_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_109_; 
lean_dec_ref_known(v___x_108_, 1);
v___x_109_ = lean_io_prim_handle_truncate(v___y_107_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v___x_110_; 
lean_dec_ref_known(v___x_109_, 1);
v___x_110_ = lean_io_prim_handle_write(v___y_107_, v_content_102_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v___x_111_; 
lean_dec_ref_known(v___x_110_, 1);
v___x_111_ = lean_io_prim_handle_flush(v___y_107_);
lean_dec(v___y_107_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v___x_112_; 
lean_dec_ref_known(v___x_111_, 1);
v___x_112_ = l___private_Lake_Util_IO_0__Lake_publishFileIfNew(v_tmpFile_105_, v_path_101_);
lean_dec_ref(v_path_101_);
lean_dec_ref(v_tmpFile_105_);
return v___x_112_;
}
else
{
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
return v___x_111_;
}
}
else
{
lean_dec(v___y_107_);
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
return v___x_110_;
}
}
else
{
lean_dec(v___y_107_);
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
return v___x_109_;
}
}
else
{
lean_dec(v___y_107_);
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
return v___x_108_;
}
}
v___jp_113_:
{
uint8_t v___x_114_; lean_object* v___x_115_; 
v___x_114_ = 3;
v___x_115_ = lean_io_prim_handle_mk(v_tmpFile_105_, v___x_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; uint8_t v___x_117_; lean_object* v___x_118_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = 1;
v___x_118_ = lean_io_prim_handle_lock(v_a_116_, v___x_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
uint8_t v___x_119_; 
lean_dec_ref_known(v___x_118_, 1);
v___x_119_ = l_System_FilePath_pathExists(v_path_101_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
v___x_120_ = lean_io_prim_handle_rewind(v_a_116_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; 
lean_dec_ref_known(v___x_120_, 1);
v___x_121_ = l_IO_FS_Handle_readBinToEnd(v_a_116_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; uint8_t v___x_123_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_121_, 1);
v___x_123_ = lean_sarray_dec_eq(v_a_122_, v_content_102_);
lean_dec(v_a_122_);
if (v___x_123_ == 0)
{
v___y_107_ = v_a_116_;
goto v___jp_106_;
}
else
{
lean_object* v___x_124_; 
lean_dec(v_a_116_);
v___x_124_ = l___private_Lake_Util_IO_0__Lake_publishFileIfNew(v_tmpFile_105_, v_path_101_);
lean_dec_ref(v_path_101_);
lean_dec_ref(v_tmpFile_105_);
return v___x_124_;
}
}
else
{
lean_dec_ref_known(v___x_121_, 1);
v___y_107_ = v_a_116_;
goto v___jp_106_;
}
}
else
{
lean_dec(v_a_116_);
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
return v___x_120_;
}
}
else
{
lean_object* v___x_125_; 
lean_dec(v_a_116_);
lean_dec_ref(v_path_101_);
v___x_125_ = lean_io_remove_file(v_tmpFile_105_);
lean_dec_ref(v_tmpFile_105_);
if (lean_obj_tag(v___x_125_) == 0)
{
return v___x_125_;
}
else
{
lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_133_; 
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; 
v_unused_134_ = lean_ctor_get(v___x_125_, 0);
lean_dec(v_unused_134_);
v___x_127_ = v___x_125_;
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
else
{
lean_dec(v___x_125_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_133_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_box(0);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 0);
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_dec(v_a_116_);
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
return v___x_118_;
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec_ref(v_tmpFile_105_);
lean_dec_ref(v_path_101_);
v_a_135_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_115_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_115_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeBinFileAtomicIfNew___boxed(lean_object* v_path_145_, lean_object* v_content_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lake_writeBinFileAtomicIfNew(v_path_145_, v_content_146_);
lean_dec_ref(v_content_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object* v_as_149_, size_t v_sz_150_, size_t v_i_151_, lean_object* v_b_152_){
_start:
{
lean_object* v_a_155_; uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_lt(v_i_151_, v_sz_150_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v_b_152_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_box(0);
v_a_162_ = lean_array_uget_borrowed(v_as_149_, v_i_151_);
lean_inc(v_a_162_);
v___x_163_ = l_IO_FS_DirEntry_path(v_a_162_);
v___x_164_ = lean_io_symlink_metadata(v___x_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; uint8_t v_type_166_; uint8_t v___x_167_; uint8_t v___x_168_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v_type_166_ = lean_ctor_get_uint8(v_a_165_, sizeof(void*)*2 + 16);
lean_dec(v_a_165_);
v___x_167_ = 0;
v___x_168_ = l_IO_FS_instBEqFileType_beq(v_type_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = l_Lake_removeFileIfExists(v___x_163_);
lean_dec_ref(v___x_163_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_dec_ref_known(v___x_169_, 1);
v_a_155_ = v___x_161_;
goto v___jp_154_;
}
else
{
return v___x_169_;
}
}
else
{
lean_object* v___x_170_; 
v___x_170_ = l_Lake_removeDirAllIfExists(v___x_163_);
lean_dec_ref(v___x_163_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_dec_ref_known(v___x_170_, 1);
v_a_155_ = v___x_161_;
goto v___jp_154_;
}
else
{
return v___x_170_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec_ref(v___x_163_);
v_a_171_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_164_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_164_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
if (lean_obj_tag(v_a_171_) == 11)
{
lean_dec_ref_known(v_a_171_, 2);
lean_del_object(v___x_173_);
v_a_155_ = v___x_161_;
goto v___jp_154_;
}
else
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
}
v___jp_154_:
{
size_t v___x_156_; size_t v___x_157_; 
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_add(v_i_151_, v___x_156_);
v_i_151_ = v___x_157_;
v_b_152_ = v_a_155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object* v_path_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_io_read_dir(v_path_179_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; size_t v_sz_184_; size_t v___x_185_; lean_object* v___x_186_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = lean_box(0);
v_sz_184_ = lean_array_size(v_a_182_);
v___x_185_ = ((size_t)0ULL);
v___x_186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_a_182_, v_sz_184_, v___x_185_, v___x_183_);
lean_dec(v_a_182_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v___x_187_; 
lean_dec_ref_known(v___x_186_, 1);
v___x_187_ = lean_io_remove_dir(v_path_179_);
if (lean_obj_tag(v___x_187_) == 0)
{
return v___x_187_;
}
else
{
lean_object* v_a_188_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
if (lean_obj_tag(v_a_188_) == 11)
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v___x_187_, 0);
lean_dec(v_unused_196_);
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 0);
lean_ctor_set(v___x_190_, 0, v___x_183_);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_183_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
return v___x_187_;
}
}
}
else
{
return v___x_186_;
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_a_197_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v___x_181_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_181_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
if (lean_obj_tag(v_a_197_) == 11)
{
lean_object* v___x_201_; lean_object* v___x_203_; 
lean_dec_ref_known(v_a_197_, 2);
v___x_201_ = lean_box(0);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 0);
lean_ctor_set(v___x_199_, 0, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
lean_object* v___x_206_; 
if (v_isShared_200_ == 0)
{
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_197_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object* v_path_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lake_removeDirAllIfExists(v_path_209_);
lean_dec_ref(v_path_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object* v_as_212_, lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_b_215_, lean_object* v___y_216_){
_start:
{
size_t v_sz_boxed_217_; size_t v_i_boxed_218_; lean_object* v_res_219_; 
v_sz_boxed_217_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_218_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_as_212_, v_sz_boxed_217_, v_i_boxed_218_, v_b_215_);
lean_dec_ref(v_as_212_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object* v_src_220_, lean_object* v_dst_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_IO_FS_readBinFile(v_src_220_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = l_IO_FS_writeBinFile(v_dst_221_, v_a_224_);
lean_dec(v_a_224_);
return v___x_225_;
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_a_226_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_223_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_223_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object* v_src_234_, lean_object* v_dst_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lake_copyFile(v_src_234_, v_dst_235_);
lean_dec_ref(v_dst_235_);
lean_dec_ref(v_src_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(lean_object* v_src_238_, lean_object* v_dst_239_, lean_object* v_as_240_, size_t v_sz_241_, size_t v_i_242_, lean_object* v_b_243_){
_start:
{
lean_object* v_a_246_; uint8_t v___x_250_; 
v___x_250_ = lean_usize_dec_lt(v_i_242_, v_sz_241_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec_ref(v_dst_239_);
lean_dec_ref(v_src_238_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v_b_243_);
return v___x_251_;
}
else
{
lean_object* v_a_252_; lean_object* v_fileName_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_a_252_ = lean_array_uget_borrowed(v_as_240_, v_i_242_);
v_fileName_253_ = lean_ctor_get(v_a_252_, 1);
v___x_254_ = lean_box(0);
lean_inc_ref_n(v_fileName_253_, 2);
lean_inc_ref(v_src_238_);
v___x_255_ = l_System_FilePath_join(v_src_238_, v_fileName_253_);
lean_inc_ref(v_dst_239_);
v___x_256_ = l_System_FilePath_join(v_dst_239_, v_fileName_253_);
v___x_257_ = l_System_FilePath_isDir(v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = l_Lake_copyFile(v___x_255_, v___x_256_);
lean_dec_ref(v___x_256_);
lean_dec_ref(v___x_255_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_dec_ref_known(v___x_258_, 1);
v_a_246_ = v___x_254_;
goto v___jp_245_;
}
else
{
lean_dec_ref(v_dst_239_);
lean_dec_ref(v_src_238_);
return v___x_258_;
}
}
else
{
lean_object* v___x_259_; 
v___x_259_ = l_Lake_copyDirAll(v___x_255_, v___x_256_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_dec_ref_known(v___x_259_, 1);
v_a_246_ = v___x_254_;
goto v___jp_245_;
}
else
{
lean_dec_ref(v_dst_239_);
lean_dec_ref(v_src_238_);
return v___x_259_;
}
}
}
v___jp_245_:
{
size_t v___x_247_; size_t v___x_248_; 
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_add(v_i_242_, v___x_247_);
v_i_242_ = v___x_248_;
v_b_243_ = v_a_246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyDirAll(lean_object* v_src_260_, lean_object* v_dst_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc_ref(v_dst_261_);
v___x_263_ = l_IO_FS_createDirAll(v_dst_261_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_264_; 
lean_dec_ref_known(v___x_263_, 1);
v___x_264_ = lean_io_read_dir(v_src_260_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; size_t v_sz_267_; size_t v___x_268_; lean_object* v___x_269_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = lean_box(0);
v_sz_267_ = lean_array_size(v_a_265_);
v___x_268_ = ((size_t)0ULL);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_260_, v_dst_261_, v_a_265_, v_sz_267_, v___x_268_, v___x_266_);
lean_dec(v_a_265_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_277_);
v___x_271_ = v___x_269_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___x_269_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_266_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_266_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
return v___x_269_;
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_dst_261_);
lean_dec_ref(v_src_260_);
v_a_278_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_264_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_264_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_dec_ref(v_dst_261_);
lean_dec_ref(v_src_260_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyDirAll___boxed(lean_object* v_src_286_, lean_object* v_dst_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_copyDirAll(v_src_286_, v_dst_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0___boxed(lean_object* v_src_290_, lean_object* v_dst_291_, lean_object* v_as_292_, lean_object* v_sz_293_, lean_object* v_i_294_, lean_object* v_b_295_, lean_object* v___y_296_){
_start:
{
size_t v_sz_boxed_297_; size_t v_i_boxed_298_; lean_object* v_res_299_; 
v_sz_boxed_297_ = lean_unbox_usize(v_sz_293_);
lean_dec(v_sz_293_);
v_i_boxed_298_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_copyDirAll_spec__0(v_src_290_, v_dst_291_, v_as_292_, v_sz_boxed_297_, v_i_boxed_298_, v_b_295_);
lean_dec_ref(v_as_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath(lean_object* v_path_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_io_realpath(v_path_301_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; uint8_t v___x_305_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v___x_305_ = l_System_FilePath_pathExists(v_a_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v_a_304_);
v___x_306_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_306_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = l_System_FilePath_normalize(v_a_304_);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; 
lean_dec_ref_known(v___x_303_, 1);
v___x_308_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object* v_path_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lake_resolvePath(v_path_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f(lean_object* v_path_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_314_ = l_Lake_resolvePath(v_path_312_);
v___x_315_ = lean_string_utf8_byte_size(v___x_314_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_nat_dec_eq(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_314_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
lean_dec_ref(v___x_314_);
v___x_319_ = lean_box(0);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object* v_path_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lake_resolvePath_x3f(v_path_320_);
return v_res_322_;
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
