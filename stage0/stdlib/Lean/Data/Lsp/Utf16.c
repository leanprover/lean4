// Lean compiler output
// Module: Lean.Data.Lsp.Utf16
// Imports: public import Lean.Data.Lsp.BasicAux public import Lean.DeclarationRange import Init.Data.String.Search
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
LEAN_EXPORT uint32_t l_Char_utf16Size(uint32_t);
LEAN_EXPORT lean_object* l_Char_utf16Size___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16Length(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeOfStx_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeOfStx_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofFilePositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_toLspRange(lean_object*);
LEAN_EXPORT uint32_t l_Char_utf16Size(uint32_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 65535;
v___x_3_ = lean_uint32_dec_le(v_c_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint32_t v___x_4_; 
v___x_4_ = 2;
return v___x_4_;
}
else
{
uint32_t v___x_5_; 
v___x_5_ = 1;
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Char_utf16Size___boxed(lean_object* v_c_6_){
_start:
{
uint32_t v_c_boxed_7_; uint32_t v_res_8_; lean_object* v_r_9_; 
v_c_boxed_7_ = lean_unbox_uint32(v_c_6_);
lean_dec(v_c_6_);
v_res_8_ = l_Char_utf16Size(v_c_boxed_7_);
v_r_9_ = lean_box_uint32(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16(uint32_t v_c_10_){
_start:
{
uint32_t v___x_11_; lean_object* v___x_12_; 
v___x_11_ = l_Char_utf16Size(v_c_10_);
v___x_12_ = lean_uint32_to_nat(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(lean_object* v_c_13_){
_start:
{
uint32_t v_c_boxed_14_; lean_object* v_res_15_; 
v_c_boxed_14_ = lean_unbox_uint32(v_c_13_);
lean_dec(v_c_13_);
v_res_15_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v_c_boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(lean_object* v___x_16_, lean_object* v_s_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_nat_dec_eq(v_a_18_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_prevPos_24_; uint32_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_sub(v_a_18_, v___x_22_);
lean_dec(v_a_18_);
v_prevPos_24_ = l_String_Slice_posLE(v___x_16_, v___x_23_);
v___x_25_ = lean_string_utf8_get_fast(v_s_17_, v_prevPos_24_);
v___x_26_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_25_);
v___x_27_ = lean_nat_add(v___x_26_, v_b_19_);
lean_dec(v_b_19_);
lean_dec(v___x_26_);
v_a_18_ = v_prevPos_24_;
v_b_19_ = v___x_27_;
goto _start;
}
else
{
lean_dec(v_a_18_);
return v_b_19_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg___boxed(lean_object* v___x_29_, lean_object* v_s_30_, lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(v___x_29_, v_s_30_, v_a_31_, v_b_32_);
lean_dec_ref(v_s_30_);
lean_dec_ref(v___x_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_String_utf16Length(lean_object* v_s_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_string_utf8_byte_size(v_s_34_);
lean_inc_ref(v_s_34_);
v___x_37_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_37_, 0, v_s_34_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
lean_ctor_set(v___x_37_, 2, v___x_36_);
v___x_38_ = l_String_Slice_revPositions(v___x_37_);
v___x_39_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(v___x_37_, v_s_34_, v___x_38_, v___x_35_);
lean_dec_ref(v_s_34_);
lean_dec_ref(v___x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(lean_object* v___x_40_, lean_object* v_s_41_, lean_object* v_inst_42_, lean_object* v_R_43_, lean_object* v_a_44_, lean_object* v_b_45_, lean_object* v_c_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(v___x_40_, v_s_41_, v_a_44_, v_b_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___boxed(lean_object* v___x_48_, lean_object* v_s_49_, lean_object* v_inst_50_, lean_object* v_R_51_, lean_object* v_a_52_, lean_object* v_b_53_, lean_object* v_c_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(v___x_48_, v_s_49_, v_inst_50_, v_R_51_, v_a_52_, v_b_53_, v_c_54_);
lean_dec_ref(v_s_49_);
lean_dec_ref(v___x_48_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(lean_object* v_s_56_, lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_zero_60_; uint8_t v_isZero_61_; 
v_zero_60_ = lean_unsigned_to_nat(0u);
v_isZero_61_ = lean_nat_dec_eq(v_x_57_, v_zero_60_);
if (v_isZero_61_ == 1)
{
lean_dec(v_x_58_);
lean_dec(v_x_57_);
return v_x_59_;
}
else
{
lean_object* v_one_62_; lean_object* v_n_63_; lean_object* v___x_64_; uint32_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_one_62_ = lean_unsigned_to_nat(1u);
v_n_63_ = lean_nat_sub(v_x_57_, v_one_62_);
lean_dec(v_x_57_);
v___x_64_ = lean_string_utf8_next(v_s_56_, v_x_58_);
v___x_65_ = lean_string_utf8_get(v_s_56_, v_x_58_);
lean_dec(v_x_58_);
v___x_66_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_65_);
v___x_67_ = lean_nat_add(v_x_59_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v_x_59_);
v_x_57_ = v_n_63_;
v_x_58_ = v___x_64_;
v_x_59_ = v___x_67_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux___boxed(lean_object* v_s_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(v_s_69_, v_x_70_, v_x_71_, v_x_72_);
lean_dec_ref(v_s_69_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom(lean_object* v_s_74_, lean_object* v_n_75_, lean_object* v_off_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(v_s_74_, v_n_75_, v_off_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16PosFrom___boxed(lean_object* v_s_79_, lean_object* v_n_80_, lean_object* v_off_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_String_codepointPosToUtf16PosFrom(v_s_79_, v_n_80_, v_off_81_);
lean_dec_ref(v_s_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos(lean_object* v_s_83_, lean_object* v_pos_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_String_codepointPosToUtf16PosFrom(v_s_83_, v_pos_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf16Pos___boxed(lean_object* v_s_87_, lean_object* v_pos_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_String_codepointPosToUtf16Pos(v_s_87_, v_pos_88_);
lean_dec_ref(v_s_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(lean_object* v_s_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_eq(v_x_91_, v___x_94_);
if (v___x_95_ == 0)
{
uint32_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_96_ = lean_string_utf8_get(v_s_90_, v_x_92_);
v___x_97_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_96_);
v___x_98_ = lean_nat_sub(v_x_91_, v___x_97_);
lean_dec(v___x_97_);
lean_dec(v_x_91_);
v___x_99_ = lean_string_utf8_next(v_s_90_, v_x_92_);
lean_dec(v_x_92_);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_x_93_, v___x_100_);
lean_dec(v_x_93_);
v_x_91_ = v___x_98_;
v_x_92_ = v___x_99_;
v_x_93_ = v___x_101_;
goto _start;
}
else
{
lean_dec(v_x_92_);
lean_dec(v_x_91_);
return v_x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(lean_object* v_s_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(v_s_103_, v_x_104_, v_x_105_, v_x_106_);
lean_dec_ref(v_s_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom(lean_object* v_s_108_, lean_object* v_utf16pos_109_, lean_object* v_off_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(v_s_108_, v_utf16pos_109_, v_off_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPosFrom___boxed(lean_object* v_s_113_, lean_object* v_utf16pos_114_, lean_object* v_off_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_String_utf16PosToCodepointPosFrom(v_s_113_, v_utf16pos_114_, v_off_115_);
lean_dec_ref(v_s_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos(lean_object* v_s_117_, lean_object* v_pos_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = l_String_utf16PosToCodepointPosFrom(v_s_117_, v_pos_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_String_utf16PosToCodepointPos___boxed(lean_object* v_s_121_, lean_object* v_pos_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_String_utf16PosToCodepointPos(v_s_121_, v_pos_122_);
lean_dec_ref(v_s_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom(lean_object* v_s_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_zero_127_; uint8_t v_isZero_128_; 
v_zero_127_ = lean_unsigned_to_nat(0u);
v_isZero_128_ = lean_nat_dec_eq(v_x_126_, v_zero_127_);
if (v_isZero_128_ == 1)
{
lean_dec(v_x_126_);
return v_x_125_;
}
else
{
lean_object* v_one_129_; lean_object* v_n_130_; lean_object* v___x_131_; 
v_one_129_ = lean_unsigned_to_nat(1u);
v_n_130_ = lean_nat_sub(v_x_126_, v_one_129_);
lean_dec(v_x_126_);
v___x_131_ = lean_string_utf8_next(v_s_124_, v_x_125_);
lean_dec(v_x_125_);
v_x_125_ = v___x_131_;
v_x_126_ = v_n_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_codepointPosToUtf8PosFrom___boxed(lean_object* v_s_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_String_codepointPosToUtf8PosFrom(v_s_133_, v_x_134_, v_x_135_);
lean_dec_ref(v_s_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(lean_object* v_text_137_, lean_object* v_line_138_){
_start:
{
lean_object* v_positions_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_positions_139_ = lean_ctor_get(v_text_137_, 1);
v___x_140_ = lean_array_get_size(v_positions_139_);
v___x_141_ = lean_nat_dec_lt(v_line_138_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_nat_dec_eq(v___x_140_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_sub(v___x_140_, v___x_144_);
v___x_146_ = lean_array_get_borrowed(v___x_142_, v_positions_139_, v___x_145_);
lean_dec(v___x_145_);
lean_inc(v___x_146_);
return v___x_146_;
}
else
{
return v___x_142_;
}
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_array_fget_borrowed(v_positions_139_, v_line_138_);
lean_inc(v___x_147_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(lean_object* v_text_148_, lean_object* v_line_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_148_, v_line_149_);
lean_dec(v_line_149_);
lean_dec_ref(v_text_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object* v_text_151_, lean_object* v_pos_152_){
_start:
{
lean_object* v_line_153_; lean_object* v_character_154_; lean_object* v_source_155_; lean_object* v_lineStartPos_156_; lean_object* v_chr_157_; lean_object* v___x_158_; 
v_line_153_ = lean_ctor_get(v_pos_152_, 0);
lean_inc(v_line_153_);
v_character_154_ = lean_ctor_get(v_pos_152_, 1);
lean_inc(v_character_154_);
lean_dec_ref(v_pos_152_);
v_source_155_ = lean_ctor_get(v_text_151_, 0);
v_lineStartPos_156_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_151_, v_line_153_);
lean_dec(v_line_153_);
lean_inc(v_lineStartPos_156_);
v_chr_157_ = l_String_utf16PosToCodepointPosFrom(v_source_155_, v_character_154_, v_lineStartPos_156_);
v___x_158_ = l_String_codepointPosToUtf8PosFrom(v_source_155_, v_lineStartPos_156_, v_chr_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos___boxed(lean_object* v_text_159_, lean_object* v_pos_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_159_, v_pos_160_);
lean_dec_ref(v_text_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object* v_text_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_line_164_; lean_object* v_column_165_; lean_object* v_source_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_177_; 
v_line_164_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_line_164_);
v_column_165_ = lean_ctor_get(v_x_163_, 1);
lean_inc(v_column_165_);
lean_dec_ref(v_x_163_);
v_source_166_ = lean_ctor_get(v_text_162_, 0);
lean_inc_ref(v_source_166_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_sub(v_line_164_, v___x_167_);
lean_dec(v_line_164_);
v___x_169_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_162_, v___x_168_);
v_isSharedCheck_177_ = !lean_is_exclusive(v_text_162_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; 
v_unused_178_ = lean_ctor_get(v_text_162_, 1);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_text_162_, 0);
lean_dec(v_unused_179_);
v___x_171_ = v_text_162_;
v_isShared_172_ = v_isSharedCheck_177_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_text_162_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_177_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = l_String_codepointPosToUtf16PosFrom(v_source_166_, v_column_165_, v___x_169_);
lean_dec_ref(v_source_166_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_173_);
lean_ctor_set(v___x_171_, 0, v___x_168_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
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
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object* v_text_180_, lean_object* v_pos_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc_ref(v_text_180_);
v___x_182_ = l_Lean_FileMap_toPosition(v_text_180_, v_pos_181_);
v___x_183_ = l_Lean_FileMap_leanPosToLspPos(v_text_180_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos___boxed(lean_object* v_text_184_, lean_object* v_pos_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_FileMap_utf8PosToLspPos(v_text_184_, v_pos_185_);
lean_dec(v_pos_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object* v_text_187_, lean_object* v_range_188_){
_start:
{
lean_object* v_start_189_; lean_object* v_stop_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_199_; 
v_start_189_ = lean_ctor_get(v_range_188_, 0);
v_stop_190_ = lean_ctor_get(v_range_188_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_range_188_);
if (v_isSharedCheck_199_ == 0)
{
v___x_192_ = v_range_188_;
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_stop_190_);
lean_inc(v_start_189_);
lean_dec(v_range_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
lean_inc_ref(v_text_187_);
v___x_194_ = l_Lean_FileMap_utf8PosToLspPos(v_text_187_, v_start_189_);
lean_dec(v_start_189_);
v___x_195_ = l_Lean_FileMap_utf8PosToLspPos(v_text_187_, v_stop_190_);
lean_dec(v_stop_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_195_);
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeOfStx_x3f(lean_object* v_text_200_, lean_object* v_stx_201_, uint8_t v_canonicalOnly_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Syntax_getRange_x3f(v_stx_201_, v_canonicalOnly_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; 
lean_dec_ref(v_text_200_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_203_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v___x_203_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_200_, v_val_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeOfStx_x3f___boxed(lean_object* v_text_214_, lean_object* v_stx_215_, lean_object* v_canonicalOnly_216_){
_start:
{
uint8_t v_canonicalOnly_boxed_217_; lean_object* v_res_218_; 
v_canonicalOnly_boxed_217_ = lean_unbox(v_canonicalOnly_216_);
v_res_218_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_214_, v_stx_215_, v_canonicalOnly_boxed_217_);
lean_dec(v_stx_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object* v_text_219_, lean_object* v_range_220_){
_start:
{
lean_object* v_start_221_; lean_object* v_end_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_231_; 
v_start_221_ = lean_ctor_get(v_range_220_, 0);
v_end_222_ = lean_ctor_get(v_range_220_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_range_220_);
if (v_isSharedCheck_231_ == 0)
{
v___x_224_ = v_range_220_;
v_isShared_225_ = v_isSharedCheck_231_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_end_222_);
lean_inc(v_start_221_);
lean_dec(v_range_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_231_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_219_, v_start_221_);
v___x_227_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_219_, v_end_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_227_);
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range___boxed(lean_object* v_text_232_, lean_object* v_range_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_232_, v_range_233_);
lean_dec_ref(v_text_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofFilePositions(lean_object* v_text_235_, lean_object* v_pos_236_, lean_object* v_endPos_237_){
_start:
{
lean_object* v___x_238_; lean_object* v_character_239_; lean_object* v___x_240_; lean_object* v_character_241_; lean_object* v___x_242_; 
lean_inc_ref(v_pos_236_);
lean_inc_ref(v_text_235_);
v___x_238_ = l_Lean_FileMap_leanPosToLspPos(v_text_235_, v_pos_236_);
v_character_239_ = lean_ctor_get(v___x_238_, 1);
lean_inc(v_character_239_);
lean_dec_ref(v___x_238_);
lean_inc_ref(v_endPos_237_);
v___x_240_ = l_Lean_FileMap_leanPosToLspPos(v_text_235_, v_endPos_237_);
v_character_241_ = lean_ctor_get(v___x_240_, 1);
lean_inc(v_character_241_);
lean_dec_ref(v___x_240_);
v___x_242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_242_, 0, v_pos_236_);
lean_ctor_set(v___x_242_, 1, v_character_239_);
lean_ctor_set(v___x_242_, 2, v_endPos_237_);
lean_ctor_set(v___x_242_, 3, v_character_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object* v_text_243_, lean_object* v_pos_244_, lean_object* v_endPos_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_inc_ref_n(v_text_243_, 2);
v___x_246_ = l_Lean_FileMap_toPosition(v_text_243_, v_pos_244_);
v___x_247_ = l_Lean_FileMap_toPosition(v_text_243_, v_endPos_245_);
v___x_248_ = l_Lean_DeclarationRange_ofFilePositions(v_text_243_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions___boxed(lean_object* v_text_249_, lean_object* v_pos_250_, lean_object* v_endPos_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_DeclarationRange_ofStringPositions(v_text_249_, v_pos_250_, v_endPos_251_);
lean_dec(v_endPos_251_);
lean_dec(v_pos_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_toLspRange(lean_object* v_r_253_){
_start:
{
lean_object* v_pos_254_; lean_object* v_endPos_255_; lean_object* v_charUtf16_256_; lean_object* v_endCharUtf16_257_; lean_object* v_line_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_278_; 
v_pos_254_ = lean_ctor_get(v_r_253_, 0);
lean_inc_ref(v_pos_254_);
v_endPos_255_ = lean_ctor_get(v_r_253_, 2);
lean_inc_ref(v_endPos_255_);
v_charUtf16_256_ = lean_ctor_get(v_r_253_, 1);
lean_inc(v_charUtf16_256_);
v_endCharUtf16_257_ = lean_ctor_get(v_r_253_, 3);
lean_inc(v_endCharUtf16_257_);
lean_dec_ref(v_r_253_);
v_line_258_ = lean_ctor_get(v_pos_254_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_pos_254_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_pos_254_, 1);
lean_dec(v_unused_279_);
v___x_260_ = v_pos_254_;
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_line_258_);
lean_dec(v_pos_254_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_278_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_line_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_276_; 
v_line_262_ = lean_ctor_get(v_endPos_255_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_endPos_255_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v_endPos_255_, 1);
lean_dec(v_unused_277_);
v___x_264_ = v_endPos_255_;
v_isShared_265_ = v_isSharedCheck_276_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_line_262_);
lean_dec(v_endPos_255_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_276_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_sub(v_line_258_, v___x_266_);
lean_dec(v_line_258_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v_charUtf16_256_);
lean_ctor_set(v___x_264_, 0, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_charUtf16_256_);
v___x_269_ = v_reuseFailAlloc_275_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_nat_sub(v_line_262_, v___x_266_);
lean_dec(v_line_262_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v_endCharUtf16_257_);
lean_ctor_set(v___x_260_, 0, v___x_270_);
v___x_272_ = v___x_260_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_endCharUtf16_257_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_269_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Utf16(builtin);
}
#ifdef __cplusplus
}
#endif
