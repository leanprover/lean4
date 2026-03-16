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
lean_object* l_Char_utf8Size(uint32_t);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_10_);
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
lean_dec_ref(v___x_27_);
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
uint32_t v___y_53_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_string_utf8_byte_size(v_s_50_);
v___x_59_ = lean_nat_dec_eq(v_p_51_, v___x_58_);
if (v___x_59_ == 0)
{
uint32_t v___x_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_60_ = lean_string_utf8_get_fast(v_s_50_, v_p_51_);
v___x_61_ = 92;
v___x_62_ = lean_uint32_dec_eq(v___x_60_, v___x_61_);
if (v___x_62_ == 0)
{
v___y_53_ = v___x_60_;
goto v___jp_52_;
}
else
{
uint32_t v___x_63_; 
v___x_63_ = 47;
v___y_53_ = v___x_63_;
goto v___jp_52_;
}
}
else
{
lean_dec(v_p_51_);
return v_s_50_;
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_inc(v_p_51_);
v___x_54_ = lean_string_utf8_set(v_s_50_, v_p_51_, v___y_53_);
v___x_55_ = l_Char_utf8Size(v___y_53_);
v___x_56_ = lean_nat_add(v_p_51_, v___x_55_);
lean_dec(v___x_55_);
lean_dec(v_p_51_);
v_s_50_ = v___x_54_;
v_p_51_ = v___x_56_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object* v_path_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = l_System_Platform_isWindows;
if (v___x_65_ == 0)
{
return v_path_64_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = l_String_mapAux___at___00Lake_mkRelPathString_spec__0(v_path_64_, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object* v_path_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = l_Lake_mkRelPathString(v_path_68_);
v___x_70_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lake_joinRelative___closed__0));
v___x_77_ = lean_string_dec_eq(v_b_75_, v___x_76_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; 
v___x_78_ = lean_string_dec_eq(v_a_74_, v___x_76_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = l_System_FilePath_join(v_a_74_, v_b_75_);
return v___x_79_;
}
else
{
lean_dec_ref(v_a_74_);
return v_b_75_;
}
}
else
{
lean_dec_ref(v_b_75_);
return v_a_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(lean_object* v_s_83_, lean_object* v_i_84_, lean_object* v_e_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_nat_dec_eq(v_i_84_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v_i_x27_88_; uint32_t v_c_89_; uint32_t v___x_90_; uint8_t v___x_91_; 
v_i_x27_88_ = lean_string_utf8_prev(v_s_83_, v_i_84_);
lean_dec(v_i_84_);
v_c_89_ = lean_string_utf8_get(v_s_83_, v_i_x27_88_);
v___x_90_ = l_System_FilePath_pathSeparator;
v___x_91_ = lean_uint32_dec_eq(v_c_89_, v___x_90_);
if (v___x_91_ == 0)
{
uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 46;
v___x_93_ = lean_uint32_dec_eq(v_c_89_, v___x_92_);
if (v___x_93_ == 0)
{
v_i_84_ = v_i_x27_88_;
goto _start;
}
else
{
lean_dec(v_e_85_);
lean_inc(v_i_x27_88_);
v_i_84_ = v_i_x27_88_;
v_e_85_ = v_i_x27_88_;
goto _start;
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_i_x27_88_);
v___x_96_ = lean_string_utf8_extract(v_s_83_, v___x_86_, v_e_85_);
lean_dec(v_e_85_);
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_i_84_);
v___x_97_ = lean_string_utf8_extract(v_s_83_, v___x_86_, v_e_85_);
lean_dec(v_e_85_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts___boxed(lean_object* v_s_98_, lean_object* v_i_99_, lean_object* v_e_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(v_s_98_, v_i_99_, v_e_100_);
lean_dec_ref(v_s_98_);
return v_res_101_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1(void){
_start:
{
uint32_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = l_System_FilePath_pathSeparator;
v___x_104_ = ((lean_object*)(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0));
v___x_105_ = lean_string_push(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
v___x_107_ = lean_string_utf8_byte_size(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(lean_object* v_s_108_){
_start:
{
lean_object* v_str_109_; lean_object* v_startInclusive_110_; lean_object* v_endExclusive_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_str_109_ = lean_ctor_get(v_s_108_, 0);
v_startInclusive_110_ = lean_ctor_get(v_s_108_, 1);
v_endExclusive_111_ = lean_ctor_get(v_s_108_, 2);
v___x_112_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
v___x_113_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2);
v___x_114_ = lean_nat_sub(v_endExclusive_111_, v_startInclusive_110_);
v___x_115_ = lean_nat_dec_le(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_dec(v___x_114_);
return v_s_108_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_sub(v___x_114_, v___x_113_);
lean_dec(v___x_114_);
v___x_118_ = lean_nat_add(v_startInclusive_110_, v___x_117_);
v___x_119_ = lean_string_memcmp(v_str_109_, v___x_112_, v___x_118_, v___x_116_, v___x_113_);
lean_dec(v___x_118_);
if (v___x_119_ == 0)
{
lean_dec(v___x_117_);
return v_s_108_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_128_; 
lean_inc(v_startInclusive_110_);
lean_inc_ref(v_str_109_);
v___x_120_ = l_String_Slice_pos_x21(v_s_108_, v___x_117_);
lean_dec(v___x_117_);
v_isSharedCheck_128_ = !lean_is_exclusive(v_s_108_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; lean_object* v_unused_130_; lean_object* v_unused_131_; 
v_unused_129_ = lean_ctor_get(v_s_108_, 2);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_s_108_, 1);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_s_108_, 0);
lean_dec(v_unused_131_);
v___x_122_ = v_s_108_;
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
else
{
lean_dec(v_s_108_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_128_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_nat_add(v_startInclusive_110_, v___x_120_);
lean_dec(v___x_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 2, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_str_109_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_startInclusive_110_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(lean_object* v_s_132_, lean_object* v_pat_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_string_utf8_byte_size(v_s_132_);
v___x_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_136_, 0, v_s_132_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_135_);
v___x_137_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0___boxed(lean_object* v_s_138_, lean_object* v_pat_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(v_s_138_, v_pat_139_);
lean_dec_ref(v_pat_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_modOfFilePath_spec__1(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
return v_x_141_;
}
else
{
lean_object* v_head_143_; lean_object* v_tail_144_; lean_object* v___x_145_; 
v_head_143_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_head_143_);
v_tail_144_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_tail_144_);
lean_dec_ref(v_x_142_);
v___x_145_ = l_Lean_Name_str___override(v_x_141_, v_head_143_);
v_x_141_ = v___x_145_;
v_x_142_ = v_tail_144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object* v_path_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_path_150_; lean_object* v___x_151_; lean_object* v_path_152_; lean_object* v_str_153_; lean_object* v_startInclusive_154_; lean_object* v_endExclusive_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_148_ = l_System_FilePath_normalize(v_path_147_);
v___x_149_ = lean_string_utf8_byte_size(v___x_148_);
v_path_150_ = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(v___x_148_, v___x_149_, v___x_149_);
lean_dec_ref(v___x_148_);
v___x_151_ = lean_obj_once(&l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1, &l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once, _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
v_path_152_ = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(v_path_150_, v___x_151_);
v_str_153_ = lean_ctor_get(v_path_152_, 0);
lean_inc_ref(v_str_153_);
v_startInclusive_154_ = lean_ctor_get(v_path_152_, 1);
lean_inc(v_startInclusive_154_);
v_endExclusive_155_ = lean_ctor_get(v_path_152_, 2);
lean_inc(v_endExclusive_155_);
lean_dec_ref(v_path_152_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_string_utf8_extract(v_str_153_, v_startInclusive_154_, v_endExclusive_155_);
lean_dec(v_endExclusive_155_);
lean_dec(v_startInclusive_154_);
lean_dec_ref(v_str_153_);
v___x_158_ = l_System_FilePath_components(v___x_157_);
v___x_159_ = l_List_foldl___at___00Lake_modOfFilePath_spec__1(v___x_156_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(lean_object* v_pat_160_, lean_object* v_s_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(v_s_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___boxed(lean_object* v_pat_163_, lean_object* v_s_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(v_pat_163_, v_s_164_);
lean_dec_ref(v_pat_163_);
return v_res_165_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
