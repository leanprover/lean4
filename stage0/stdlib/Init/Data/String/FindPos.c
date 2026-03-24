// Lean compiler output
// Module: Init.Data.String.FindPos
// Imports: public import Init.Data.String.Basic import Init.Omega import Init.Data.String.OrderInstances import Init.Data.String.Lemmas.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_String_Pos_Raw_isValidForSlice(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posGT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_posLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_Pos_prev_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Init.Data.String.FindPos"};
static const lean_object* l_String_Slice_Pos_prev_x21___closed__0 = (const lean_object*)&l_String_Slice_Pos_prev_x21___closed__0_value;
static const lean_string_object l_String_Slice_Pos_prev_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "String.Slice.Pos.prev!"};
static const lean_object* l_String_Slice_Pos_prev_x21___closed__1 = (const lean_object*)&l_String_Slice_Pos_prev_x21___closed__1_value;
static const lean_string_object l_String_Slice_Pos_prev_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "The start position has no previous position"};
static const lean_object* l_String_Slice_Pos_prev_x21___closed__2 = (const lean_object*)&l_String_Slice_Pos_prev_x21___closed__2_value;
static lean_once_cell_t l_String_Slice_Pos_prev_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_Pos_prev_x21___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prev_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg(lean_object* v_s_1_, lean_object* v_offset_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = l_String_Pos_Raw_isValidForSlice(v_s_1_, v_offset_2_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_add(v_offset_2_, v___x_4_);
lean_dec(v_offset_2_);
v_offset_2_ = v___x_5_;
goto _start;
}
else
{
return v_offset_2_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGE___redArg___boxed(lean_object* v_s_7_, lean_object* v_offset_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_String_Slice_posGE___redArg(v_s_7_, v_offset_8_);
lean_dec_ref(v_s_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGE(lean_object* v_s_10_, lean_object* v_offset_11_, lean_object* v_h_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_String_Slice_posGE___redArg(v_s_10_, v_offset_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGE___boxed(lean_object* v_s_14_, lean_object* v_offset_15_, lean_object* v_h_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_String_Slice_posGE(v_s_14_, v_offset_15_, v_h_16_);
lean_dec_ref(v_s_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg(lean_object* v_s_18_, lean_object* v_offset_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_nat_add(v_offset_19_, v___x_20_);
v___x_22_ = l_String_Slice_posGE___redArg(v_s_18_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT___redArg___boxed(lean_object* v_s_23_, lean_object* v_offset_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_String_Slice_posGT___redArg(v_s_23_, v_offset_24_);
lean_dec(v_offset_24_);
lean_dec_ref(v_s_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT(lean_object* v_s_26_, lean_object* v_offset_27_, lean_object* v_h_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_add(v_offset_27_, v___x_29_);
v___x_31_ = l_String_Slice_posGE___redArg(v_s_26_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posGT___boxed(lean_object* v_s_32_, lean_object* v_offset_33_, lean_object* v_h_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_String_Slice_posGT(v_s_32_, v_offset_33_, v_h_34_);
lean_dec(v_offset_33_);
lean_dec_ref(v_s_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg(lean_object* v_offset_36_, lean_object* v_s_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_add(v_offset_36_, v___x_38_);
v___x_40_ = l_String_Slice_posGE___redArg(v_s_37_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___redArg___boxed(lean_object* v_offset_41_, lean_object* v_s_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_String_Slice_findNextPos___redArg(v_offset_41_, v_s_42_);
lean_dec_ref(v_s_42_);
lean_dec(v_offset_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos(lean_object* v_offset_44_, lean_object* v_s_45_, lean_object* v_h_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_String_Slice_findNextPos___redArg(v_offset_44_, v_s_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_findNextPos___boxed(lean_object* v_offset_48_, lean_object* v_s_49_, lean_object* v_h_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_String_Slice_findNextPos(v_offset_48_, v_s_49_, v_h_50_);
lean_dec_ref(v_s_49_);
lean_dec(v_offset_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_String_posGE___redArg(lean_object* v_s_52_, lean_object* v_offset_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = lean_string_utf8_byte_size(v_s_52_);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v_s_52_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_55_);
v___x_57_ = l_String_Slice_posGE___redArg(v___x_56_, v_offset_53_);
lean_dec_ref(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_String_posGE(lean_object* v_s_58_, lean_object* v_offset_59_, lean_object* v_h_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_string_utf8_byte_size(v_s_58_);
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v_s_58_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_62_);
v___x_64_ = l_String_Slice_posGE___redArg(v___x_63_, v_offset_59_);
lean_dec_ref(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_posGT___redArg(lean_object* v_s_65_, lean_object* v_offset_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_string_utf8_byte_size(v_s_65_);
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_s_65_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_68_);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_offset_66_, v___x_70_);
v___x_72_ = l_String_Slice_posGE___redArg(v___x_69_, v___x_71_);
lean_dec_ref(v___x_69_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_String_posGT___redArg___boxed(lean_object* v_s_73_, lean_object* v_offset_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_String_posGT___redArg(v_s_73_, v_offset_74_);
lean_dec(v_offset_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_String_posGT(lean_object* v_s_76_, lean_object* v_offset_77_, lean_object* v_h_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_string_utf8_byte_size(v_s_76_);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v_s_76_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_offset_77_, v___x_82_);
v___x_84_ = l_String_Slice_posGE___redArg(v___x_81_, v___x_83_);
lean_dec_ref(v___x_81_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_String_posGT___boxed(lean_object* v_s_85_, lean_object* v_offset_86_, lean_object* v_h_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_String_posGT(v_s_85_, v_offset_86_, v_h_87_);
lean_dec(v_offset_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLE(lean_object* v_s_89_, lean_object* v_offset_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = l_String_Pos_Raw_isValidForSlice(v_s_89_, v_offset_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_sub(v_offset_90_, v___x_92_);
lean_dec(v_offset_90_);
v_offset_90_ = v___x_93_;
goto _start;
}
else
{
return v_offset_90_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLE___boxed(lean_object* v_s_95_, lean_object* v_offset_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_String_Slice_posLE(v_s_95_, v_offset_96_);
lean_dec_ref(v_s_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg(lean_object* v_s_98_, lean_object* v_offset_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_sub(v_offset_99_, v___x_100_);
v___x_102_ = l_String_Slice_posLE(v_s_98_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT___redArg___boxed(lean_object* v_s_103_, lean_object* v_offset_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_String_Slice_posLT___redArg(v_s_103_, v_offset_104_);
lean_dec(v_offset_104_);
lean_dec_ref(v_s_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT(lean_object* v_s_106_, lean_object* v_offset_107_, lean_object* v___h_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_sub(v_offset_107_, v___x_109_);
v___x_111_ = l_String_Slice_posLE(v_s_106_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_posLT___boxed(lean_object* v_s_112_, lean_object* v_offset_113_, lean_object* v___h_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_String_Slice_posLT(v_s_112_, v_offset_113_, v___h_114_);
lean_dec(v_offset_113_);
lean_dec_ref(v_s_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_String_posLE(lean_object* v_s_116_, lean_object* v_offset_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_string_utf8_byte_size(v_s_116_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v_s_116_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
v___x_121_ = l_String_Slice_posLE(v___x_120_, v_offset_117_);
lean_dec_ref(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_String_posLT___redArg(lean_object* v_s_122_, lean_object* v_offset_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_string_utf8_byte_size(v_s_122_);
v___x_126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_126_, 0, v_s_122_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
lean_ctor_set(v___x_126_, 2, v___x_125_);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_sub(v_offset_123_, v___x_127_);
v___x_129_ = l_String_Slice_posLE(v___x_126_, v___x_128_);
lean_dec_ref(v___x_126_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_String_posLT___redArg___boxed(lean_object* v_s_130_, lean_object* v_offset_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_String_posLT___redArg(v_s_130_, v_offset_131_);
lean_dec(v_offset_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_String_posLT(lean_object* v_s_133_, lean_object* v_offset_134_, lean_object* v_h_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_string_utf8_byte_size(v_s_133_);
v___x_138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_138_, 0, v_s_133_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_137_);
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_sub(v_offset_134_, v___x_139_);
v___x_141_ = l_String_Slice_posLE(v___x_138_, v___x_140_);
lean_dec_ref(v___x_138_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_String_posLT___boxed(lean_object* v_s_142_, lean_object* v_offset_143_, lean_object* v_h_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_String_posLT(v_s_142_, v_offset_143_, v_h_144_);
lean_dec(v_offset_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg(lean_object* v_s_146_, lean_object* v_pos_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_sub(v_pos_147_, v___x_148_);
v___x_150_ = l_String_Slice_posLE(v_s_146_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___redArg___boxed(lean_object* v_s_151_, lean_object* v_pos_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_String_Slice_Pos_prev___redArg(v_s_151_, v_pos_152_);
lean_dec(v_pos_152_);
lean_dec_ref(v_s_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev(lean_object* v_s_154_, lean_object* v_pos_155_, lean_object* v_h_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_sub(v_pos_155_, v___x_157_);
v___x_159_ = l_String_Slice_posLE(v_s_154_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev___boxed(lean_object* v_s_160_, lean_object* v_pos_161_, lean_object* v_h_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_String_Slice_Pos_prev(v_s_160_, v_pos_161_, v_h_162_);
lean_dec(v_pos_161_);
lean_dec_ref(v_s_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f(lean_object* v_s_164_, lean_object* v_pos_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_nat_dec_eq(v_pos_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_sub(v_pos_165_, v___x_168_);
v___x_170_ = l_String_Slice_posLE(v_s_164_, v___x_169_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x3f___boxed(lean_object* v_s_173_, lean_object* v_pos_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_String_Slice_Pos_prev_x3f(v_s_173_, v_pos_174_);
lean_dec(v_pos_174_);
lean_dec_ref(v_s_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(lean_object* v_msg_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_panic_fn(v___x_177_, v_msg_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0(lean_object* v_s_179_, lean_object* v_msg_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(v_msg_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_Pos_prev_x21_spec__0___boxed(lean_object* v_s_182_, lean_object* v_msg_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0(v_s_182_, v_msg_183_);
lean_dec_ref(v_s_182_);
return v_res_184_;
}
}
static lean_object* _init_l_String_Slice_Pos_prev_x21___closed__3(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_188_ = ((lean_object*)(l_String_Slice_Pos_prev_x21___closed__2));
v___x_189_ = lean_unsigned_to_nat(31u);
v___x_190_ = lean_unsigned_to_nat(115u);
v___x_191_ = ((lean_object*)(l_String_Slice_Pos_prev_x21___closed__1));
v___x_192_ = ((lean_object*)(l_String_Slice_Pos_prev_x21___closed__0));
v___x_193_ = l_mkPanicMessageWithDecl(v___x_192_, v___x_191_, v___x_190_, v___x_189_, v___x_188_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21(lean_object* v_s_194_, lean_object* v_pos_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_nat_dec_eq(v_pos_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_sub(v_pos_195_, v___x_198_);
v___x_200_ = l_String_Slice_posLE(v_s_194_, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l_String_Slice_Pos_prev_x21___closed__3, &l_String_Slice_Pos_prev_x21___closed__3_once, _init_l_String_Slice_Pos_prev_x21___closed__3);
v___x_202_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prev_x21___boxed(lean_object* v_s_203_, lean_object* v_pos_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_String_Slice_Pos_prev_x21(v_s_203_, v_pos_204_);
lean_dec(v_pos_204_);
lean_dec_ref(v_s_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg(lean_object* v_s_206_, lean_object* v_pos_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_string_utf8_byte_size(v_s_206_);
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_s_206_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v_pos_207_, v___x_211_);
v___x_213_ = l_String_Slice_posLE(v___x_210_, v___x_212_);
lean_dec_ref(v___x_210_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev___redArg___boxed(lean_object* v_s_214_, lean_object* v_pos_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_String_Pos_prev___redArg(v_s_214_, v_pos_215_);
lean_dec(v_pos_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev(lean_object* v_s_217_, lean_object* v_pos_218_, lean_object* v_h_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_string_utf8_byte_size(v_s_217_);
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v_s_217_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_sub(v_pos_218_, v___x_223_);
v___x_225_ = l_String_Slice_posLE(v___x_222_, v___x_224_);
lean_dec_ref(v___x_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev___boxed(lean_object* v_s_226_, lean_object* v_pos_227_, lean_object* v_h_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_String_Pos_prev(v_s_226_, v_pos_227_, v_h_228_);
lean_dec(v_pos_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f(lean_object* v_s_230_, lean_object* v_pos_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_string_utf8_byte_size(v_s_230_);
v___x_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_234_, 0, v_s_230_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = l_String_Slice_Pos_prev_x3f(v___x_234_, v_pos_231_);
lean_dec_ref(v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_235_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_dec(v___x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_val_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x3f___boxed(lean_object* v_s_245_, lean_object* v_pos_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_String_Pos_prev_x3f(v_s_245_, v_pos_246_);
lean_dec(v_pos_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x21(lean_object* v_s_248_, lean_object* v_pos_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_string_utf8_byte_size(v_s_248_);
v___x_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_252_, 0, v_s_248_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
lean_ctor_set(v___x_252_, 2, v___x_251_);
v___x_253_ = l_String_Slice_Pos_prev_x21(v___x_252_, v_pos_249_);
lean_dec_ref(v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prev_x21___boxed(lean_object* v_s_254_, lean_object* v_pos_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_String_Pos_prev_x21(v_s_254_, v_pos_255_);
lean_dec(v_pos_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn(lean_object* v_s_257_, lean_object* v_p_258_, lean_object* v_n_259_){
_start:
{
lean_object* v_zero_260_; uint8_t v_isZero_261_; 
v_zero_260_ = lean_unsigned_to_nat(0u);
v_isZero_261_ = lean_nat_dec_eq(v_n_259_, v_zero_260_);
if (v_isZero_261_ == 1)
{
lean_dec(v_n_259_);
return v_p_258_;
}
else
{
lean_object* v_one_262_; lean_object* v_n_263_; uint8_t v___x_268_; 
v_one_262_ = lean_unsigned_to_nat(1u);
v_n_263_ = lean_nat_sub(v_n_259_, v_one_262_);
lean_dec(v_n_259_);
v___x_268_ = lean_nat_dec_eq(v_p_258_, v_zero_260_);
if (v___x_268_ == 0)
{
goto v___jp_264_;
}
else
{
if (v_isZero_261_ == 0)
{
lean_dec(v_n_263_);
return v_p_258_;
}
else
{
goto v___jp_264_;
}
}
v___jp_264_:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_nat_sub(v_p_258_, v_one_262_);
lean_dec(v_p_258_);
v___x_266_ = l_String_Slice_posLE(v_s_257_, v___x_265_);
v_p_258_ = v___x_266_;
v_n_259_ = v_n_263_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_prevn___boxed(lean_object* v_s_269_, lean_object* v_p_270_, lean_object* v_n_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_String_Slice_Pos_prevn(v_s_269_, v_p_270_, v_n_271_);
lean_dec_ref(v_s_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_prevn(lean_object* v_s_273_, lean_object* v_p_274_, lean_object* v_n_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_string_utf8_byte_size(v_s_273_);
v___x_278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_278_, 0, v_s_273_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
lean_ctor_set(v___x_278_, 2, v___x_277_);
v___x_279_ = l_String_Slice_Pos_prevn(v___x_278_, v_p_274_, v_n_275_);
lean_dec_ref(v___x_278_);
return v___x_279_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_FindPos(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_FindPos(builtin);
}
#ifdef __cplusplus
}
#endif
