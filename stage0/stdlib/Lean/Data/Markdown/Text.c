// Lean compiler output
// Module: Lean.Data.Markdown.Text
// Imports: public import Init.Prelude import Init.While import Init.Data.String.Basic import Init.Data.String.Slice.Basic import Init.Data.String.Length public import Init.Data.String.Subslice import Lean.Data.Html.CharRef
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
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Html_numericCharacterReference_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Html_namedCharacterReference_x3f(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_isAsciiControl(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_isAsciiControl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_isAsciiPunctuation(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_isAsciiPunctuation___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Markdown_characterReference_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Markdown_characterReference_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_characterReference_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Markdown_characterReference_x3f___closed__0 = (const lean_object*)&l_Lean_Markdown_characterReference_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_characterReference_x3f___closed__1___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_characterReference_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_characterReference_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Markdown_characterReference_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_characterReference_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_isCharacterReferenceChar(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_isCharacterReferenceChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Text_0__Lean_Markdown_maxCharacterReferenceLength;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_decodeCharacterReference_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Markdown_decodeText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_characterReference_x3f___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_decodeText___closed__0 = (const lean_object*)&l_Lean_Markdown_decodeText___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_decodeText(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_isAsciiControl(uint32_t v_c_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_2_ = lean_uint32_to_nat(v_c_1_);
v___x_3_ = lean_unsigned_to_nat(32u);
v___x_4_ = lean_nat_dec_lt(v___x_2_, v___x_3_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(127u);
v___x_6_ = lean_nat_dec_eq(v___x_2_, v___x_5_);
lean_dec(v___x_2_);
return v___x_6_;
}
else
{
lean_dec(v___x_2_);
return v___x_4_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_isAsciiControl___boxed(lean_object* v_c_7_){
_start:
{
uint32_t v_c_boxed_8_; uint8_t v_res_9_; lean_object* v_r_10_; 
v_c_boxed_8_ = lean_unbox_uint32(v_c_7_);
lean_dec(v_c_7_);
v_res_9_ = l_Lean_Markdown_isAsciiControl(v_c_boxed_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_isAsciiPunctuation(uint32_t v_c_11_){
_start:
{
lean_object* v_n_12_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_n_12_ = lean_uint32_to_nat(v_c_11_);
v___x_28_ = lean_unsigned_to_nat(33u);
v___x_29_ = lean_nat_dec_le(v___x_28_, v_n_12_);
if (v___x_29_ == 0)
{
goto v___jp_23_;
}
else
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(47u);
v___x_31_ = lean_nat_dec_le(v_n_12_, v___x_30_);
if (v___x_31_ == 0)
{
goto v___jp_23_;
}
else
{
lean_dec(v_n_12_);
return v___x_31_;
}
}
v___jp_13_:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(123u);
v___x_15_ = lean_nat_dec_le(v___x_14_, v_n_12_);
if (v___x_15_ == 0)
{
lean_dec(v_n_12_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(126u);
v___x_17_ = lean_nat_dec_le(v_n_12_, v___x_16_);
lean_dec(v_n_12_);
return v___x_17_;
}
}
v___jp_18_:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_unsigned_to_nat(91u);
v___x_20_ = lean_nat_dec_le(v___x_19_, v_n_12_);
if (v___x_20_ == 0)
{
goto v___jp_13_;
}
else
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(96u);
v___x_22_ = lean_nat_dec_le(v_n_12_, v___x_21_);
if (v___x_22_ == 0)
{
goto v___jp_13_;
}
else
{
lean_dec(v_n_12_);
return v___x_22_;
}
}
}
v___jp_23_:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(58u);
v___x_25_ = lean_nat_dec_le(v___x_24_, v_n_12_);
if (v___x_25_ == 0)
{
goto v___jp_18_;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(64u);
v___x_27_ = lean_nat_dec_le(v_n_12_, v___x_26_);
if (v___x_27_ == 0)
{
goto v___jp_18_;
}
else
{
lean_dec(v_n_12_);
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_isAsciiPunctuation___boxed(lean_object* v_c_32_){
_start:
{
uint32_t v_c_boxed_33_; uint8_t v_res_34_; lean_object* v_r_35_; 
v_c_boxed_33_ = lean_unbox_uint32(v_c_32_);
lean_dec(v_c_32_);
v_res_34_ = l_Lean_Markdown_isAsciiPunctuation(v_c_boxed_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Markdown_characterReference_x3f_spec__0(lean_object* v_x_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
if (lean_obj_tag(v_x_37_) == 0)
{
uint8_t v___x_38_; 
v___x_38_ = 1;
return v___x_38_;
}
else
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
}
else
{
if (lean_obj_tag(v_x_37_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 0;
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v_val_42_; uint32_t v___x_43_; uint32_t v___x_44_; uint8_t v___x_45_; 
v_val_41_ = lean_ctor_get(v_x_36_, 0);
v_val_42_ = lean_ctor_get(v_x_37_, 0);
v___x_43_ = lean_unbox_uint32(v_val_41_);
v___x_44_ = lean_unbox_uint32(v_val_42_);
v___x_45_ = lean_uint32_dec_eq(v___x_43_, v___x_44_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Markdown_characterReference_x3f_spec__0___boxed(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_instBEqOption_beq___at___00Lean_Markdown_characterReference_x3f_spec__0(v_x_46_, v_x_47_);
lean_dec(v_x_47_);
lean_dec(v_x_46_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
static lean_object* _init_l_Lean_Markdown_characterReference_x3f___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_51_; lean_object* v___x_52_; 
v___x_51_ = 35;
v___x_52_ = lean_box_uint32(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Markdown_characterReference_x3f___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = l_Lean_Markdown_characterReference_x3f___closed__1___boxed__const__1;
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_characterReference_x3f(lean_object* v_s_55_, lean_object* v_body_56_){
_start:
{
lean_object* v___y_58_; lean_object* v_startInclusive_65_; lean_object* v_endExclusive_66_; lean_object* v_str_67_; lean_object* v_startInclusive_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_125_; 
v_startInclusive_65_ = lean_ctor_get(v_body_56_, 0);
v_endExclusive_66_ = lean_ctor_get(v_body_56_, 1);
v_str_67_ = lean_ctor_get(v_s_55_, 0);
v_startInclusive_68_ = lean_ctor_get(v_s_55_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_s_55_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; 
v_unused_126_ = lean_ctor_get(v_s_55_, 2);
lean_dec(v_unused_126_);
v___x_70_ = v_s_55_;
v_isShared_71_ = v_isSharedCheck_125_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_startInclusive_68_);
lean_inc(v_str_67_);
lean_dec(v_s_55_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_125_;
goto v_resetjp_69_;
}
v___jp_57_:
{
uint32_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = l_Char_ofNat(v___y_58_);
lean_dec(v___y_58_);
v___x_60_ = ((lean_object*)(l_Lean_Markdown_characterReference_x3f___closed__0));
v___x_61_ = lean_string_push(v___x_60_, v___x_59_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
v___jp_63_:
{
lean_object* v___x_64_; 
v___x_64_ = lean_unsigned_to_nat(65533u);
v___y_58_ = v___x_64_;
goto v___jp_57_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_text_75_; 
v___x_72_ = lean_nat_add(v_startInclusive_68_, v_startInclusive_65_);
v___x_73_ = lean_nat_add(v_startInclusive_68_, v_endExclusive_66_);
lean_dec(v_startInclusive_68_);
lean_inc(v___x_73_);
lean_inc(v___x_72_);
lean_inc_ref(v_str_67_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 2, v___x_73_);
lean_ctor_set(v___x_70_, 1, v___x_72_);
v_text_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_str_67_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v___x_73_);
v_text_75_ = v_reuseFailAlloc_124_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_76_ = lean_unsigned_to_nat(31u);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l_String_Slice_Pos_nextn(v_text_75_, v___x_77_, v___x_76_);
v___x_79_ = lean_nat_add(v___x_72_, v___x_78_);
lean_dec(v___x_78_);
lean_inc(v___x_73_);
lean_inc_ref(v_str_67_);
v___x_80_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_80_, 0, v_str_67_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
lean_ctor_set(v___x_80_, 2, v___x_73_);
v___x_81_ = l_String_Slice_Pos_get_x3f(v___x_80_, v___x_77_);
lean_dec_ref_known(v___x_80_, 3);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v___x_82_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_82_ = lean_string_utf8_extract_fast(v_str_67_, v___x_72_, v___x_73_);
v___x_103_ = l_String_Slice_Pos_get_x3f(v_text_75_, v___x_77_);
v___x_104_ = lean_obj_once(&l_Lean_Markdown_characterReference_x3f___closed__1, &l_Lean_Markdown_characterReference_x3f___closed__1_once, _init_l_Lean_Markdown_characterReference_x3f___closed__1);
v___x_105_ = l_instBEqOption_beq___at___00Lean_Markdown_characterReference_x3f_spec__0(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_dec_ref(v_text_75_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
lean_dec_ref(v_str_67_);
v___x_106_ = l_Lean_Html_namedCharacterReference_x3f(v___x_82_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_112_ = l_String_Slice_Pos_nextn(v_text_75_, v___x_77_, v___x_107_);
lean_dec_ref(v_text_75_);
v___x_113_ = lean_nat_add(v___x_72_, v___x_112_);
lean_dec(v___x_112_);
lean_dec(v___x_72_);
v___x_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_114_, 0, v_str_67_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_ctor_set(v___x_114_, 2, v___x_73_);
v___x_115_ = l_String_Slice_Pos_get_x3f(v___x_114_, v___x_77_);
lean_dec_ref_known(v___x_114_, 3);
if (lean_obj_tag(v___x_115_) == 1)
{
lean_object* v_val_116_; uint32_t v___x_117_; uint32_t v___x_118_; uint8_t v___x_119_; 
v_val_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = 120;
v___x_118_ = lean_unbox_uint32(v_val_116_);
v___x_119_ = lean_uint32_dec_eq(v___x_118_, v___x_117_);
if (v___x_119_ == 0)
{
uint32_t v___x_120_; uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = 88;
v___x_121_ = lean_unbox_uint32(v_val_116_);
lean_dec(v_val_116_);
v___x_122_ = lean_uint32_dec_eq(v___x_121_, v___x_120_);
if (v___x_122_ == 0)
{
goto v___jp_108_;
}
else
{
goto v___jp_98_;
}
}
else
{
lean_dec(v_val_116_);
goto v___jp_98_;
}
}
else
{
lean_dec(v___x_115_);
goto v___jp_108_;
}
v___jp_108_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_string_length(v___x_82_);
v___x_110_ = lean_nat_sub(v___x_109_, v___x_107_);
v___x_111_ = lean_unsigned_to_nat(7u);
v___y_84_ = v___x_110_;
v___y_85_ = v___x_111_;
goto v___jp_83_;
}
}
v___jp_83_:
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_le(v___y_84_, v___y_85_);
lean_dec(v___y_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec_ref(v___x_82_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Html_numericCharacterReference_x3f(v___x_82_);
lean_dec_ref(v___x_82_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
else
{
lean_object* v_val_90_; uint8_t v___x_91_; 
v_val_90_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v___x_88_, 1);
v___x_91_ = lean_nat_dec_eq(v_val_90_, v___x_77_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(55296u);
v___x_93_ = lean_nat_dec_lt(v_val_90_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(57343u);
v___x_95_ = lean_nat_dec_lt(v___x_94_, v_val_90_);
if (v___x_95_ == 0)
{
lean_dec(v_val_90_);
goto v___jp_63_;
}
else
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(1114112u);
v___x_97_ = lean_nat_dec_lt(v_val_90_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_val_90_);
goto v___jp_63_;
}
else
{
v___y_58_ = v_val_90_;
goto v___jp_57_;
}
}
}
else
{
v___y_58_ = v_val_90_;
goto v___jp_57_;
}
}
else
{
lean_dec(v_val_90_);
goto v___jp_63_;
}
}
}
}
v___jp_98_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_string_length(v___x_82_);
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_nat_sub(v___x_99_, v___x_100_);
v___x_102_ = lean_unsigned_to_nat(6u);
v___y_84_ = v___x_101_;
v___y_85_ = v___x_102_;
goto v___jp_83_;
}
}
else
{
lean_object* v___x_123_; 
lean_dec_ref_known(v___x_81_, 1);
lean_dec_ref(v_text_75_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
lean_dec_ref(v_str_67_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_characterReference_x3f___boxed(lean_object* v_s_127_, lean_object* v_body_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Markdown_characterReference_x3f(v_s_127_, v_body_128_);
lean_dec_ref(v_body_128_);
return v_res_129_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_isCharacterReferenceChar(uint32_t v_c_130_){
_start:
{
uint32_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = 65;
v___x_145_ = lean_uint32_dec_le(v___x_144_, v_c_130_);
if (v___x_145_ == 0)
{
goto v___jp_139_;
}
else
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 90;
v___x_147_ = lean_uint32_dec_le(v_c_130_, v___x_146_);
if (v___x_147_ == 0)
{
goto v___jp_139_;
}
else
{
return v___x_147_;
}
}
v___jp_131_:
{
uint32_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = 35;
v___x_133_ = lean_uint32_dec_eq(v_c_130_, v___x_132_);
return v___x_133_;
}
v___jp_134_:
{
uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_135_ = 48;
v___x_136_ = lean_uint32_dec_le(v___x_135_, v_c_130_);
if (v___x_136_ == 0)
{
goto v___jp_131_;
}
else
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 57;
v___x_138_ = lean_uint32_dec_le(v_c_130_, v___x_137_);
if (v___x_138_ == 0)
{
goto v___jp_131_;
}
else
{
return v___x_138_;
}
}
}
v___jp_139_:
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 97;
v___x_141_ = lean_uint32_dec_le(v___x_140_, v_c_130_);
if (v___x_141_ == 0)
{
goto v___jp_134_;
}
else
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 122;
v___x_143_ = lean_uint32_dec_le(v_c_130_, v___x_142_);
if (v___x_143_ == 0)
{
goto v___jp_134_;
}
else
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_isCharacterReferenceChar___boxed(lean_object* v_c_148_){
_start:
{
uint32_t v_c_boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_c_boxed_149_ = lean_unbox_uint32(v_c_148_);
lean_dec(v_c_148_);
v_res_150_ = l_Lean_Markdown_isCharacterReferenceChar(v_c_boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Text_0__Lean_Markdown_maxCharacterReferenceLength(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(31u);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg(lean_object* v_s_155_, lean_object* v_i_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_snd_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_222_; 
v_snd_158_ = lean_ctor_get(v_a_157_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_a_157_, 0);
lean_dec(v_unused_223_);
v___x_160_ = v_a_157_;
v_isShared_161_ = v_isSharedCheck_222_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snd_158_);
lean_dec(v_a_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_222_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_221_; 
v_fst_162_ = lean_ctor_get(v_snd_158_, 0);
v_snd_163_ = lean_ctor_get(v_snd_158_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_snd_158_);
if (v_isSharedCheck_221_ == 0)
{
v___x_165_ = v_snd_158_;
v_isShared_166_ = v_isSharedCheck_221_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_snd_163_);
lean_inc(v_fst_162_);
lean_dec(v_snd_158_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_221_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_str_175_; lean_object* v_startInclusive_176_; lean_object* v_endExclusive_177_; lean_object* v___y_179_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v_decide_201_; 
v_str_175_ = lean_ctor_get(v_s_155_, 0);
v_startInclusive_176_ = lean_ctor_get(v_s_155_, 1);
v_endExclusive_177_ = lean_ctor_get(v_s_155_, 2);
v___x_199_ = lean_box(0);
v___x_200_ = lean_nat_sub(v_endExclusive_177_, v_startInclusive_176_);
v_decide_201_ = lean_nat_dec_eq(v_fst_162_, v___x_200_);
lean_dec(v___x_200_);
if (v_decide_201_ == 0)
{
lean_object* v___x_202_; uint32_t v___x_203_; uint32_t v___x_204_; uint8_t v___x_205_; 
v___x_202_ = lean_nat_add(v_startInclusive_176_, v_fst_162_);
v___x_203_ = lean_string_utf8_get_fast(v_str_175_, v___x_202_);
v___x_204_ = 59;
v___x_205_ = lean_uint32_dec_eq(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = l_Lean_Markdown_isCharacterReferenceChar(v___x_203_);
if (v___x_206_ == 0)
{
lean_dec(v___x_202_);
lean_dec(v_i_156_);
lean_dec_ref(v_s_155_);
goto v___jp_167_;
}
else
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(31u);
v___x_208_ = lean_nat_dec_le(v___x_207_, v_snd_163_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_del_object(v___x_165_);
lean_dec(v_fst_162_);
lean_del_object(v___x_160_);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_snd_163_, v___x_209_);
lean_dec(v_snd_163_);
v___x_211_ = lean_string_utf8_next_fast(v_str_175_, v___x_202_);
lean_dec(v___x_202_);
v___x_212_ = lean_nat_sub(v___x_211_, v_startInclusive_176_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_210_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_199_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v_a_157_ = v___x_214_;
goto _start;
}
else
{
lean_dec(v___x_202_);
lean_dec(v_i_156_);
lean_dec_ref(v_s_155_);
goto v___jp_167_;
}
}
}
else
{
uint8_t v___x_216_; 
lean_inc(v_startInclusive_176_);
lean_inc_ref(v_str_175_);
lean_dec(v___x_202_);
lean_del_object(v___x_165_);
lean_del_object(v___x_160_);
v___x_216_ = lean_nat_dec_le(v_i_156_, v_fst_162_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_inc(v_i_156_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_i_156_);
lean_ctor_set(v___x_217_, 1, v_i_156_);
v___y_179_ = v___x_217_;
goto v___jp_178_;
}
else
{
lean_object* v___x_218_; 
lean_inc(v_fst_162_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_i_156_);
lean_ctor_set(v___x_218_, 1, v_fst_162_);
v___y_179_ = v___x_218_;
goto v___jp_178_;
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_del_object(v___x_165_);
lean_del_object(v___x_160_);
lean_dec(v_i_156_);
lean_dec_ref(v_s_155_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_fst_162_);
lean_ctor_set(v___x_219_, 1, v_snd_163_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_199_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
v___jp_167_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg___closed__0));
if (v_isShared_166_ == 0)
{
v___x_170_ = v___x_165_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_fst_162_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_snd_163_);
v___x_170_ = v_reuseFailAlloc_174_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_170_);
lean_ctor_set(v___x_160_, 0, v___x_168_);
v___x_172_ = v___x_160_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Markdown_characterReference_x3f(v_s_155_, v___y_179_);
lean_dec_ref(v___y_179_);
if (lean_obj_tag(v___x_180_) == 1)
{
lean_object* v_val_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_195_; 
v_val_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_195_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_val_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_185_ = lean_nat_add(v_startInclusive_176_, v_fst_162_);
v___x_186_ = lean_string_utf8_next_fast(v_str_175_, v___x_185_);
lean_dec(v___x_185_);
lean_dec_ref(v_str_175_);
v___x_187_ = lean_nat_sub(v___x_186_, v_startInclusive_176_);
lean_dec(v_startInclusive_176_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_val_181_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_188_);
v___x_190_ = v___x_183_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_fst_162_);
lean_ctor_set(v___x_192_, 1, v_snd_163_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v___x_180_);
lean_dec(v_startInclusive_176_);
lean_dec_ref(v_str_175_);
v___x_196_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg___closed__0));
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v_fst_162_);
lean_ctor_set(v___x_197_, 1, v_snd_163_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_decodeCharacterReference_x3f(lean_object* v_s_224_, lean_object* v_i_225_){
_start:
{
lean_object* v_len_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_fst_231_; 
v_len_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_box(0);
lean_inc(v_i_225_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v_i_225_);
lean_ctor_set(v___x_228_, 1, v_len_226_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg(v_s_224_, v_i_225_, v___x_229_);
v_fst_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_fst_231_);
lean_dec_ref(v___x_230_);
if (lean_obj_tag(v_fst_231_) == 0)
{
return v___x_227_;
}
else
{
lean_object* v_val_232_; 
v_val_232_ = lean_ctor_get(v_fst_231_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v_fst_231_, 1);
return v_val_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0(lean_object* v_s_233_, lean_object* v_i_234_, lean_object* v_inst_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeCharacterReference_x3f_spec__0___redArg(v_s_233_, v_i_234_, v_a_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg(lean_object* v_s_238_, lean_object* v_text_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_301_; 
v_fst_241_ = lean_ctor_get(v_a_240_, 0);
v_snd_242_ = lean_ctor_get(v_a_240_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_a_240_);
if (v_isSharedCheck_301_ == 0)
{
v___x_244_ = v_a_240_;
v_isShared_245_ = v_isSharedCheck_301_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_snd_242_);
lean_inc(v_fst_241_);
lean_dec(v_a_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_301_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_startInclusive_246_; lean_object* v_endExclusive_247_; lean_object* v___x_248_; uint8_t v_decide_249_; 
v_startInclusive_246_ = lean_ctor_get(v_s_238_, 1);
v_endExclusive_247_ = lean_ctor_get(v_s_238_, 2);
v___x_248_ = lean_nat_sub(v_endExclusive_247_, v_startInclusive_246_);
v_decide_249_ = lean_nat_dec_eq(v_snd_242_, v___x_248_);
if (v_decide_249_ == 0)
{
uint32_t v___x_250_; lean_object* v___x_251_; uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_250_ = lean_string_utf8_get_fast(v_text_239_, v_snd_242_);
v___x_251_ = lean_string_utf8_next_fast(v_text_239_, v_snd_242_);
lean_dec(v_snd_242_);
v___x_252_ = 92;
v___x_253_ = lean_uint32_dec_eq(v___x_250_, v___x_252_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint8_t v___x_255_; 
lean_dec(v___x_248_);
v___x_254_ = 38;
v___x_255_ = lean_uint32_dec_eq(v___x_250_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = lean_string_push(v_fst_241_, v___x_250_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_251_);
lean_ctor_set(v___x_244_, 0, v___x_256_);
v___x_258_ = v___x_244_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_251_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
v_a_240_ = v___x_258_;
goto _start;
}
}
else
{
lean_object* v___x_261_; 
lean_inc_ref(v_s_238_);
v___x_261_ = l_Lean_Markdown_decodeCharacterReference_x3f(v_s_238_, v___x_251_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_string_push(v_fst_241_, v___x_250_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_251_);
lean_ctor_set(v___x_244_, 0, v___x_262_);
v___x_264_ = v___x_244_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_251_);
v___x_264_ = v_reuseFailAlloc_266_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
v_a_240_ = v___x_264_;
goto _start;
}
}
else
{
lean_object* v_val_267_; lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
lean_del_object(v___x_244_);
v_val_267_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v___x_261_, 1);
v_fst_268_ = lean_ctor_get(v_val_267_, 0);
v_snd_269_ = lean_ctor_get(v_val_267_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_val_267_);
if (v_isSharedCheck_278_ == 0)
{
v___x_271_ = v_val_267_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_snd_269_);
lean_inc(v_fst_268_);
lean_dec(v_val_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_string_append(v_fst_241_, v_fst_268_);
lean_dec(v_fst_268_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_snd_269_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
v_a_240_ = v___x_275_;
goto _start;
}
}
}
}
}
else
{
uint8_t v_decide_279_; 
v_decide_279_ = lean_nat_dec_eq(v___x_251_, v___x_248_);
lean_dec(v___x_248_);
if (v_decide_279_ == 0)
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_string_utf8_get_fast(v_text_239_, v___x_251_);
v___x_281_ = l_Lean_Markdown_isAsciiPunctuation(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_string_push(v_fst_241_, v___x_250_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_251_);
lean_ctor_set(v___x_244_, 0, v___x_282_);
v___x_284_ = v___x_244_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_251_);
v___x_284_ = v_reuseFailAlloc_286_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v_a_240_ = v___x_284_;
goto _start;
}
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_287_ = lean_string_push(v_fst_241_, v___x_280_);
v___x_288_ = lean_string_utf8_next_fast(v_text_239_, v___x_251_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_288_);
lean_ctor_set(v___x_244_, 0, v___x_287_);
v___x_290_ = v___x_244_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
v_a_240_ = v___x_290_;
goto _start;
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_string_push(v_fst_241_, v___x_250_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_251_);
lean_ctor_set(v___x_244_, 0, v___x_293_);
v___x_295_ = v___x_244_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_251_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_240_ = v___x_295_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v___x_248_);
lean_dec_ref(v_s_238_);
if (v_isShared_245_ == 0)
{
v___x_299_ = v___x_244_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_fst_241_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_snd_242_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg___boxed(lean_object* v_s_302_, lean_object* v_text_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg(v_s_302_, v_text_303_, v_a_304_);
lean_dec_ref(v_text_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_decodeText(lean_object* v_text_309_){
_start:
{
lean_object* v_i_310_; lean_object* v___x_311_; lean_object* v_s_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_fst_315_; 
v_i_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_string_utf8_byte_size(v_text_309_);
lean_inc_ref(v_text_309_);
v_s_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_s_312_, 0, v_text_309_);
lean_ctor_set(v_s_312_, 1, v_i_310_);
lean_ctor_set(v_s_312_, 2, v___x_311_);
v___x_313_ = ((lean_object*)(l_Lean_Markdown_decodeText___closed__0));
v___x_314_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg(v_s_312_, v_text_309_, v___x_313_);
lean_dec_ref(v_text_309_);
v_fst_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_fst_315_);
lean_dec_ref(v___x_314_);
return v_fst_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0(lean_object* v_s_316_, lean_object* v_text_317_, lean_object* v_inst_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___redArg(v_s_316_, v_text_317_, v_a_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0___boxed(lean_object* v_s_321_, lean_object* v_text_322_, lean_object* v_inst_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_decodeText_spec__0(v_s_321_, v_text_322_, v_inst_323_, v_a_324_);
lean_dec_ref(v_text_322_);
return v_res_325_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_CharRef(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Text(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_CharRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Markdown_characterReference_x3f___closed__1___boxed__const__1 = _init_l_Lean_Markdown_characterReference_x3f___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_characterReference_x3f___closed__1___boxed__const__1);
l___private_Lean_Data_Markdown_Text_0__Lean_Markdown_maxCharacterReferenceLength = _init_l___private_Lean_Data_Markdown_Text_0__Lean_Markdown_maxCharacterReferenceLength();
lean_mark_persistent(l___private_Lean_Data_Markdown_Text_0__Lean_Markdown_maxCharacterReferenceLength);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Text(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_CharRef(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Text(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_CharRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Text(builtin);
}
#ifdef __cplusplus
}
#endif
