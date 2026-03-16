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
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_createParentDirs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeFileIfExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_3_);
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
lean_dec_ref(v_a_14_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(lean_object* v_as_27_, size_t v_sz_28_, size_t v_i_29_, lean_object* v_b_30_){
_start:
{
lean_object* v_a_33_; uint8_t v___x_37_; 
v___x_37_ = lean_usize_dec_lt(v_i_29_, v_sz_28_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v_b_30_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; lean_object* v_a_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_box(0);
v_a_40_ = lean_array_uget_borrowed(v_as_27_, v_i_29_);
lean_inc(v_a_40_);
v___x_41_ = l_IO_FS_DirEntry_path(v_a_40_);
v___x_42_ = lean_io_symlink_metadata(v___x_41_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; uint8_t v_type_44_; uint8_t v___x_45_; uint8_t v___x_46_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref(v___x_42_);
v_type_44_ = lean_ctor_get_uint8(v_a_43_, sizeof(void*)*2 + 16);
lean_dec(v_a_43_);
v___x_45_ = 0;
v___x_46_ = l_IO_FS_instBEqFileType_beq(v_type_44_, v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
v___x_47_ = l_Lake_removeFileIfExists(v___x_41_);
lean_dec_ref(v___x_41_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_dec_ref(v___x_47_);
v_a_33_ = v___x_39_;
goto v___jp_32_;
}
else
{
return v___x_47_;
}
}
else
{
lean_object* v___x_48_; 
v___x_48_ = l_Lake_removeDirAllIfExists(v___x_41_);
lean_dec_ref(v___x_41_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_dec_ref(v___x_48_);
v_a_33_ = v___x_39_;
goto v___jp_32_;
}
else
{
return v___x_48_;
}
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
lean_dec_ref(v___x_41_);
v_a_49_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_42_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_42_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
if (lean_obj_tag(v_a_49_) == 11)
{
lean_dec_ref(v_a_49_);
lean_del_object(v___x_51_);
v_a_33_ = v___x_39_;
goto v___jp_32_;
}
else
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
v___jp_32_:
{
size_t v___x_34_; size_t v___x_35_; 
v___x_34_ = ((size_t)1ULL);
v___x_35_ = lean_usize_add(v_i_29_, v___x_34_);
v_i_29_ = v___x_35_;
v_b_30_ = v_a_33_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists(lean_object* v_path_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_io_read_dir(v_path_57_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; size_t v_sz_62_; size_t v___x_63_; lean_object* v___x_64_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = lean_box(0);
v_sz_62_ = lean_array_size(v_a_60_);
v___x_63_ = ((size_t)0ULL);
v___x_64_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_a_60_, v_sz_62_, v___x_63_, v___x_61_);
lean_dec(v_a_60_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; 
lean_dec_ref(v___x_64_);
v___x_65_ = lean_io_remove_dir(v_path_57_);
if (lean_obj_tag(v___x_65_) == 0)
{
return v___x_65_;
}
else
{
lean_object* v_a_66_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
if (lean_obj_tag(v_a_66_) == 11)
{
lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
lean_dec_ref(v_a_66_);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; 
v_unused_74_ = lean_ctor_get(v___x_65_, 0);
lean_dec(v_unused_74_);
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set_tag(v___x_68_, 0);
lean_ctor_set(v___x_68_, 0, v___x_61_);
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_61_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
lean_dec(v_a_66_);
return v___x_65_;
}
}
}
else
{
return v___x_64_;
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_86_; 
v_a_75_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_86_ == 0)
{
v___x_77_ = v___x_59_;
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_59_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
if (lean_obj_tag(v_a_75_) == 11)
{
lean_object* v___x_79_; lean_object* v___x_81_; 
lean_dec_ref(v_a_75_);
v___x_79_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 0);
lean_ctor_set(v___x_77_, 0, v___x_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
else
{
lean_object* v___x_84_; 
if (v_isShared_78_ == 0)
{
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_75_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_removeDirAllIfExists___boxed(lean_object* v_path_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lake_removeDirAllIfExists(v_path_87_);
lean_dec_ref(v_path_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(lean_object* v_as_90_, lean_object* v_sz_91_, lean_object* v_i_92_, lean_object* v_b_93_, lean_object* v___y_94_){
_start:
{
size_t v_sz_boxed_95_; size_t v_i_boxed_96_; lean_object* v_res_97_; 
v_sz_boxed_95_ = lean_unbox_usize(v_sz_91_);
lean_dec(v_sz_91_);
v_i_boxed_96_ = lean_unbox_usize(v_i_92_);
lean_dec(v_i_92_);
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_as_90_, v_sz_boxed_95_, v_i_boxed_96_, v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile(lean_object* v_src_98_, lean_object* v_dst_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_IO_FS_readBinFile(v_src_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = l_IO_FS_writeBinFile(v_dst_99_, v_a_102_);
lean_dec(v_a_102_);
return v___x_103_;
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_101_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_101_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_copyFile___boxed(lean_object* v_src_112_, lean_object* v_dst_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lake_copyFile(v_src_112_, v_dst_113_);
lean_dec_ref(v_dst_113_);
lean_dec_ref(v_src_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath(lean_object* v_path_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_io_realpath(v_path_117_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; uint8_t v___x_121_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref(v___x_119_);
v___x_121_ = l_System_FilePath_pathExists(v_a_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_a_120_);
v___x_122_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_122_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = l_System_FilePath_normalize(v_a_120_);
return v___x_123_;
}
}
else
{
lean_object* v___x_124_; 
lean_dec_ref(v___x_119_);
v___x_124_ = ((lean_object*)(l_Lake_resolvePath___closed__0));
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath___boxed(lean_object* v_path_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_resolvePath(v_path_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f(lean_object* v_path_128_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_130_ = l_Lake_resolvePath(v_path_128_);
v___x_131_ = lean_string_utf8_byte_size(v___x_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_130_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
lean_dec_ref(v___x_130_);
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolvePath_x3f___boxed(lean_object* v_path_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_resolvePath_x3f(v_path_136_);
return v_res_138_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
