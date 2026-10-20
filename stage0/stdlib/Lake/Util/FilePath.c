// Lean compiler output
// Module: Lake.Util.FilePath
// Imports: public import Lean.Data.Json import Init.Data.String.TakeDrop import Init.Data.String.Modify import Init.System.Platform
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
lean_object* lean_string_utf8_byte_size(lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern uint8_t l_System_Platform_isWindows;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_relPathFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_relPathFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_mkRelPathString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToJsonFilePath__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToJsonFilePath__lake___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonFilePath__lake___closed__0 = (const lean_object*)&l_Lake_instToJsonFilePath__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonFilePath__lake = (const lean_object*)&l_Lake_instToJsonFilePath__lake___closed__0_value;
static const lean_string_object l_Lake_joinRelative___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_joinRelative___closed__0 = (const lean_object*)&l_Lake_joinRelative___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instDivFilePath__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_joinRelative, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDivFilePath__lake___closed__0 = (const lean_object*)&l_Lake_instDivFilePath__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDivFilePath__lake = (const lean_object*)&l_Lake_instDivFilePath__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instHDivFilePathString__lake = (const lean_object*)&l_Lake_instDivFilePath__lake___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_modOfFilePath_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(lean_object* v___x_1_, lean_object* v_s_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_string_utf8_byte_size(v_s_2_);
v___x_4_ = lean_string_utf8_byte_size(v___x_1_);
v___x_5_ = lean_nat_dec_le(v___x_4_, v___x_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
lean_dec_ref(v_s_2_);
v___x_6_ = lean_box(0);
return v___x_6_;
}
else
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_string_memcmp(v_s_2_, v___x_1_, v___x_7_, v___x_7_, v___x_4_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v_s_2_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc_ref(v_s_2_);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v_s_2_);
lean_ctor_set(v___x_10_, 1, v___x_7_);
lean_ctor_set(v___x_10_, 2, v___x_3_);
v___x_11_ = l_String_Slice_pos_x21(v___x_10_, v___x_4_);
lean_dec_ref_known(v___x_10_, 3);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v_s_2_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_ctor_set(v___x_12_, 2, v___x_3_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg___boxed(lean_object* v___x_14_, lean_object* v_s_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(v___x_14_, v_s_15_);
lean_dec_ref(v___x_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(lean_object* v___x_17_, lean_object* v_s_18_, lean_object* v_pat_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(v___x_17_, v_s_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___boxed(lean_object* v___x_21_, lean_object* v_s_22_, lean_object* v_pat_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(v___x_21_, v_s_22_, v_pat_23_);
lean_dec_ref(v_pat_23_);
lean_dec_ref(v___x_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_relPathFrom(lean_object* v_root_25_, lean_object* v_path_26_){
_start:
{
lean_object* v___x_27_; 
lean_inc_ref(v_path_26_);
v___x_27_ = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(v_root_25_, v_path_26_);
if (lean_obj_tag(v___x_27_) == 1)
{
lean_object* v_val_28_; lean_object* v_str_29_; lean_object* v_startInclusive_30_; lean_object* v_endExclusive_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_43_; 
lean_dec_ref(v_path_26_);
v_val_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v___x_27_, 1);
v_str_29_ = lean_ctor_get(v_val_28_, 0);
lean_inc_ref(v_str_29_);
v_startInclusive_30_ = lean_ctor_get(v_val_28_, 1);
lean_inc(v_startInclusive_30_);
v_endExclusive_31_ = lean_ctor_get(v_val_28_, 2);
lean_inc(v_endExclusive_31_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = l_String_Slice_Pos_nextn(v_val_28_, v___x_33_, v___x_32_);
v_isSharedCheck_43_ = !lean_is_exclusive(v_val_28_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; lean_object* v_unused_45_; lean_object* v_unused_46_; 
v_unused_44_ = lean_ctor_get(v_val_28_, 2);
lean_dec(v_unused_44_);
v_unused_45_ = lean_ctor_get(v_val_28_, 1);
lean_dec(v_unused_45_);
v_unused_46_ = lean_ctor_get(v_val_28_, 0);
lean_dec(v_unused_46_);
v___x_36_ = v_val_28_;
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
else
{
lean_dec(v_val_28_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lean_nat_add(v_startInclusive_30_, v___x_34_);
lean_dec(v___x_34_);
lean_dec(v_startInclusive_30_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_str_29_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v_endExclusive_31_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = l_String_Slice_toString(v___x_40_);
lean_dec_ref(v___x_40_);
return v___x_41_;
}
}
}
else
{
lean_dec(v___x_27_);
return v_path_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_relPathFrom___boxed(lean_object* v_root_47_, lean_object* v_path_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lake_relPathFrom(v_root_47_, v_path_48_);
lean_dec_ref(v_root_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lake_mkRelPathString_spec__0(lean_object* v_s_50_, lean_object* v_p_51_){
_start:
{
lean_object* v___y_53_; lean_object* v___y_54_; uint32_t v___y_58_; lean_object* v___x_70_; uint8_t v_decide_71_; 
v___x_70_ = lean_string_utf8_byte_size(v_s_50_);
v_decide_71_ = lean_nat_dec_eq(v_p_51_, v___x_70_);
if (v_decide_71_ == 0)
{
uint32_t v___x_72_; uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_72_ = lean_string_utf8_get_fast(v_s_50_, v_p_51_);
v___x_73_ = 92;
v___x_74_ = lean_uint32_dec_eq(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
v___y_58_ = v___x_72_;
goto v___jp_57_;
}
else
{
uint32_t v___x_75_; 
v___x_75_ = 47;
v___y_58_ = v___x_75_;
goto v___jp_57_;
}
}
else
{
lean_dec(v_p_51_);
return v_s_50_;
}
v___jp_52_:
{
lean_object* v___x_55_; 
v___x_55_ = lean_nat_add(v_p_51_, v___y_54_);
lean_dec(v_p_51_);
v_s_50_ = v___y_53_;
v_p_51_ = v___x_55_;
goto _start;
}
v___jp_57_:
{
lean_object* v___x_59_; uint32_t v___x_60_; uint8_t v___x_61_; 
lean_inc(v_p_51_);
v___x_59_ = lean_string_utf8_set(v_s_50_, v_p_51_, v___y_58_);
v___x_60_ = 127;
v___x_61_ = lean_uint32_dec_le(v___y_58_, v___x_60_);
if (v___x_61_ == 0)
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 2047;
v___x_63_ = lean_uint32_dec_le(v___y_58_, v___x_62_);
if (v___x_63_ == 0)
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 65535;
v___x_65_ = lean_uint32_dec_le(v___y_58_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lean_unsigned_to_nat(4u);
v___y_53_ = v___x_59_;
v___y_54_ = v___x_66_;
goto v___jp_52_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(3u);
v___y_53_ = v___x_59_;
v___y_54_ = v___x_67_;
goto v___jp_52_;
}
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(2u);
v___y_53_ = v___x_59_;
v___y_54_ = v___x_68_;
goto v___jp_52_;
}
}
else
{
lean_object* v___x_69_; 
v___x_69_ = lean_unsigned_to_nat(1u);
v___y_53_ = v___x_59_;
v___y_54_ = v___x_69_;
goto v___jp_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object* v_path_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = l_System_Platform_isWindows;
if (v___x_77_ == 0)
{
return v_path_76_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = l_String_mapAux___at___00Lake_mkRelPathString_spec__0(v_path_76_, v___x_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object* v_path_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = l_Lake_mkRelPathString(v_path_80_);
v___x_82_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object* v_a_86_, lean_object* v_b_87_){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lake_joinRelative___closed__0));
v___x_89_ = lean_string_dec_eq(v_b_87_, v___x_88_);
if (v___x_89_ == 0)
{
uint8_t v___x_90_; 
v___x_90_ = lean_string_dec_eq(v_a_86_, v___x_88_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = l_System_FilePath_join(v_a_86_, v_b_87_);
return v___x_91_;
}
else
{
lean_dec_ref(v_a_86_);
return v_b_87_;
}
}
else
{
lean_dec_ref(v_b_87_);
return v_a_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(lean_object* v_s_95_, lean_object* v_i_96_, lean_object* v_e_97_){
_start:
{
lean_object* v___x_98_; uint8_t v_decide_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v_decide_99_ = lean_nat_dec_eq(v_i_96_, v___x_98_);
if (v_decide_99_ == 0)
{
lean_object* v_i_x27_100_; uint32_t v_c_101_; uint32_t v___x_102_; uint8_t v___x_103_; 
v_i_x27_100_ = lean_string_utf8_prev(v_s_95_, v_i_96_);
lean_dec(v_i_96_);
v_c_101_ = lean_string_utf8_get(v_s_95_, v_i_x27_100_);
v___x_102_ = l_System_FilePath_pathSeparator;
v___x_103_ = lean_uint32_dec_eq(v_c_101_, v___x_102_);
if (v___x_103_ == 0)
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = 46;
v___x_105_ = lean_uint32_dec_eq(v_c_101_, v___x_104_);
if (v___x_105_ == 0)
{
v_i_96_ = v_i_x27_100_;
goto _start;
}
else
{
lean_dec(v_e_97_);
lean_inc(v_i_x27_100_);
v_i_96_ = v_i_x27_100_;
v_e_97_ = v_i_x27_100_;
goto _start;
}
}
else
{
lean_object* v___x_108_; 
lean_dec(v_i_x27_100_);
v___x_108_ = lean_string_utf8_extract(v_s_95_, v___x_98_, v_e_97_);
lean_dec(v_e_97_);
return v___x_108_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec(v_i_96_);
v___x_109_ = lean_string_utf8_extract(v_s_95_, v___x_98_, v_e_97_);
lean_dec(v_e_97_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts___boxed(lean_object* v_s_110_, lean_object* v_i_111_, lean_object* v_e_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(v_s_110_, v_i_111_, v_e_112_);
lean_dec_ref(v_s_110_);
return v_res_113_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1(void){
_start:
{
uint32_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = l_System_FilePath_pathSeparator;
v___x_116_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0));
v___x_117_ = lean_string_push(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
v___x_119_ = lean_string_utf8_byte_size(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(lean_object* v_s_120_){
_start:
{
lean_object* v_str_121_; lean_object* v_startInclusive_122_; lean_object* v_endExclusive_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_str_121_ = lean_ctor_get(v_s_120_, 0);
v_startInclusive_122_ = lean_ctor_get(v_s_120_, 1);
v_endExclusive_123_ = lean_ctor_get(v_s_120_, 2);
v___x_124_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
v___x_125_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2);
v___x_126_ = lean_nat_sub(v_endExclusive_123_, v_startInclusive_122_);
v___x_127_ = lean_nat_dec_le(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v___x_126_);
return v_s_120_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_sub(v___x_126_, v___x_125_);
lean_dec(v___x_126_);
v___x_130_ = lean_nat_add(v_startInclusive_122_, v___x_129_);
v___x_131_ = lean_string_memcmp(v_str_121_, v___x_124_, v___x_130_, v___x_128_, v___x_125_);
lean_dec(v___x_130_);
if (v___x_131_ == 0)
{
lean_dec(v___x_129_);
return v_s_120_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
lean_inc(v_startInclusive_122_);
lean_inc_ref(v_str_121_);
v___x_132_ = l_String_Slice_pos_x21(v_s_120_, v___x_129_);
lean_dec(v___x_129_);
v_isSharedCheck_140_ = !lean_is_exclusive(v_s_120_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; lean_object* v_unused_142_; lean_object* v_unused_143_; 
v_unused_141_ = lean_ctor_get(v_s_120_, 2);
lean_dec(v_unused_141_);
v_unused_142_ = lean_ctor_get(v_s_120_, 1);
lean_dec(v_unused_142_);
v_unused_143_ = lean_ctor_get(v_s_120_, 0);
lean_dec(v_unused_143_);
v___x_134_ = v_s_120_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_dec(v_s_120_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_nat_add(v_startInclusive_122_, v___x_132_);
lean_dec(v___x_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 2, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_str_121_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_startInclusive_122_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(lean_object* v_s_144_, lean_object* v_pat_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_string_utf8_byte_size(v_s_144_);
v___x_148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_148_, 0, v_s_144_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
v___x_149_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0___boxed(lean_object* v_s_150_, lean_object* v_pat_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(v_s_150_, v_pat_151_);
lean_dec_ref(v_pat_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_modOfFilePath_spec__1(lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
return v_x_153_;
}
else
{
lean_object* v_head_155_; lean_object* v_tail_156_; lean_object* v___x_157_; 
v_head_155_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_head_155_);
v_tail_156_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_tail_156_);
lean_dec_ref_known(v_x_154_, 2);
v___x_157_ = l_Lean_Name_str___override(v_x_153_, v_head_155_);
v_x_153_ = v___x_157_;
v_x_154_ = v_tail_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object* v_path_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_path_162_; lean_object* v___x_163_; lean_object* v_path_164_; lean_object* v_str_165_; lean_object* v_startInclusive_166_; lean_object* v_endExclusive_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_160_ = l_System_FilePath_normalize(v_path_159_);
v___x_161_ = lean_string_utf8_byte_size(v___x_160_);
v_path_162_ = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(v___x_160_, v___x_161_, v___x_161_);
lean_dec_ref(v___x_160_);
v___x_163_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
v_path_164_ = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(v_path_162_, v___x_163_);
v_str_165_ = lean_ctor_get(v_path_164_, 0);
lean_inc_ref(v_str_165_);
v_startInclusive_166_ = lean_ctor_get(v_path_164_, 1);
lean_inc(v_startInclusive_166_);
v_endExclusive_167_ = lean_ctor_get(v_path_164_, 2);
lean_inc(v_endExclusive_167_);
lean_dec_ref(v_path_164_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_string_utf8_extract_fast(v_str_165_, v_startInclusive_166_, v_endExclusive_167_);
lean_dec(v_endExclusive_167_);
lean_dec(v_startInclusive_166_);
lean_dec_ref(v_str_165_);
v___x_170_ = l_System_FilePath_components(v___x_169_);
v___x_171_ = l_List_foldl___at___00Lake_modOfFilePath_spec__1(v___x_168_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(lean_object* v_pat_172_, lean_object* v_s_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(v_s_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___boxed(lean_object* v_pat_175_, lean_object* v_s_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(v_pat_175_, v_s_176_);
lean_dec_ref(v_pat_175_);
return v_res_177_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_FilePath(builtin);
}
#ifdef __cplusplus
}
#endif
