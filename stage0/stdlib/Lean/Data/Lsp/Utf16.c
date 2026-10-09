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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_revPositions(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT uint32_t l_Lean_Char_utf16Size(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Char_utf16Size___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_utf16Length(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_codepointPosToUtf16PosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_codepointPosToUtf16PosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16PosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16Pos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_utf16PosToCodepointPosFromAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_utf16PosToCodepointPosFromAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPosFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf8PosFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf8PosFrom___boxed(lean_object*, lean_object*, lean_object*);
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
uint32_t l_Lean_Char_utf16Size(uint32_t v_c_1_){
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
LEAN_EXPORT void l_Lean_Char_utf16Size_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
uint32_t v_res_6_;
v_res_6_ = l_Lean_Char_utf16Size(v_c_1_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Char_utf16Size___boxed(lean_object* v_c_7_){
_start:
{
uint32_t v_c_boxed_8_; uint32_t v_res_9_; lean_object* v_r_10_; 
v_c_boxed_8_ = lean_unbox_uint32(v_c_7_);
lean_dec(v_c_7_);
v_res_9_ = l_Lean_Char_utf16Size(v_c_boxed_8_);
v_r_10_ = lean_box_uint32(v_res_9_);
return v_r_10_;
}
}
lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(uint32_t v_c_11_){
_start:
{
uint32_t v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Char_utf16Size(v_c_11_);
v___x_13_ = lean_uint32_to_nat(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_11_ = stack[0].m_num;
lean_object* v_res_14_;
v_res_14_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(v_c_11_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16___boxed(lean_object* v_c_15_){
_start:
{
uint32_t v_c_boxed_16_; lean_object* v_res_17_; 
v_c_boxed_16_ = lean_unbox_uint32(v_c_15_);
lean_dec(v_c_15_);
v_res_17_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(v_c_boxed_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg(lean_object* v___x_18_, lean_object* v_s_19_, lean_object* v_a_20_, lean_object* v_b_21_){
_start:
{
lean_object* v___x_22_; uint8_t v_decide_23_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v_decide_23_ = lean_nat_dec_eq(v_a_20_, v___x_22_);
if (v_decide_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_prevPos_26_; uint32_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_sub(v_a_20_, v___x_24_);
lean_dec(v_a_20_);
v_prevPos_26_ = l_String_Slice_posLE(v___x_18_, v___x_25_);
v___x_27_ = lean_string_utf8_get_fast(v_s_19_, v_prevPos_26_);
v___x_28_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(v___x_27_);
v___x_29_ = lean_nat_add(v___x_28_, v_b_21_);
lean_dec(v_b_21_);
lean_dec(v___x_28_);
v_a_20_ = v_prevPos_26_;
v_b_21_ = v___x_29_;
goto _start;
}
else
{
lean_dec(v_a_20_);
return v_b_21_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg___boxed(lean_object* v___x_31_, lean_object* v_s_32_, lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg(v___x_31_, v_s_32_, v_a_33_, v_b_34_);
lean_dec_ref(v_s_32_);
lean_dec_ref(v___x_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_utf16Length(lean_object* v_s_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_string_utf8_byte_size(v_s_36_);
lean_inc_ref(v_s_36_);
v___x_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_39_, 0, v_s_36_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_38_);
v___x_40_ = l_String_Slice_revPositions(v___x_39_);
v___x_41_ = l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg(v___x_39_, v_s_36_, v___x_40_, v___x_37_);
lean_dec_ref(v_s_36_);
lean_dec_ref_known(v___x_39_, 3);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0(lean_object* v___x_42_, lean_object* v_s_43_, lean_object* v_inst_44_, lean_object* v_R_45_, lean_object* v_a_46_, lean_object* v_b_47_, lean_object* v_c_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___redArg(v___x_42_, v_s_43_, v_a_46_, v_b_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0___boxed(lean_object* v___x_50_, lean_object* v_s_51_, lean_object* v_inst_52_, lean_object* v_R_53_, lean_object* v_a_54_, lean_object* v_b_55_, lean_object* v_c_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_WellFounded_opaqueFix_u2083___at___00Lean_String_utf16Length_spec__0(v___x_50_, v_s_51_, v_inst_52_, v_R_53_, v_a_54_, v_b_55_, v_c_56_);
lean_dec_ref(v_s_51_);
lean_dec_ref(v___x_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_codepointPosToUtf16PosFromAux(lean_object* v_s_58_, lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_zero_62_; uint8_t v_isZero_63_; 
v_zero_62_ = lean_unsigned_to_nat(0u);
v_isZero_63_ = lean_nat_dec_eq(v_x_59_, v_zero_62_);
if (v_isZero_63_ == 1)
{
lean_dec(v_x_60_);
lean_dec(v_x_59_);
return v_x_61_;
}
else
{
lean_object* v_one_64_; lean_object* v_n_65_; lean_object* v___x_66_; uint32_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_one_64_ = lean_unsigned_to_nat(1u);
v_n_65_ = lean_nat_sub(v_x_59_, v_one_64_);
lean_dec(v_x_59_);
v___x_66_ = lean_string_utf8_next(v_s_58_, v_x_60_);
v___x_67_ = lean_string_utf8_get(v_s_58_, v_x_60_);
lean_dec(v_x_60_);
v___x_68_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(v___x_67_);
v___x_69_ = lean_nat_add(v_x_61_, v___x_68_);
lean_dec(v___x_68_);
lean_dec(v_x_61_);
v_x_59_ = v_n_65_;
v_x_60_ = v___x_66_;
v_x_61_ = v___x_69_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_codepointPosToUtf16PosFromAux___boxed(lean_object* v_s_71_, lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_codepointPosToUtf16PosFromAux(v_s_71_, v_x_72_, v_x_73_, v_x_74_);
lean_dec_ref(v_s_71_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16PosFrom(lean_object* v_s_76_, lean_object* v_n_77_, lean_object* v_off_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_codepointPosToUtf16PosFromAux(v_s_76_, v_n_77_, v_off_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16PosFrom___boxed(lean_object* v_s_81_, lean_object* v_n_82_, lean_object* v_off_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_String_codepointPosToUtf16PosFrom(v_s_81_, v_n_82_, v_off_83_);
lean_dec_ref(v_s_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16Pos(lean_object* v_s_85_, lean_object* v_pos_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_Lean_String_codepointPosToUtf16PosFrom(v_s_85_, v_pos_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf16Pos___boxed(lean_object* v_s_89_, lean_object* v_pos_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_String_codepointPosToUtf16Pos(v_s_89_, v_pos_90_);
lean_dec_ref(v_s_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_utf16PosToCodepointPosFromAux(lean_object* v_s_92_, lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_nat_dec_eq(v_x_93_, v___x_96_);
if (v___x_97_ == 0)
{
uint32_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = lean_string_utf8_get(v_s_92_, v_x_94_);
v___x_99_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_csize16(v___x_98_);
v___x_100_ = lean_nat_sub(v_x_93_, v___x_99_);
lean_dec(v___x_99_);
lean_dec(v_x_93_);
v___x_101_ = lean_string_utf8_next(v_s_92_, v_x_94_);
lean_dec(v_x_94_);
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_x_95_, v___x_102_);
lean_dec(v_x_95_);
v_x_93_ = v___x_100_;
v_x_94_ = v___x_101_;
v_x_95_ = v___x_103_;
goto _start;
}
else
{
lean_dec(v_x_94_);
lean_dec(v_x_93_);
return v_x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_String_utf16PosToCodepointPosFromAux___boxed(lean_object* v_s_105_, lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_utf16PosToCodepointPosFromAux(v_s_105_, v_x_106_, v_x_107_, v_x_108_);
lean_dec_ref(v_s_105_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPosFrom(lean_object* v_s_110_, lean_object* v_utf16pos_111_, lean_object* v_off_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_String_utf16PosToCodepointPosFromAux(v_s_110_, v_utf16pos_111_, v_off_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPosFrom___boxed(lean_object* v_s_115_, lean_object* v_utf16pos_116_, lean_object* v_off_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_String_utf16PosToCodepointPosFrom(v_s_115_, v_utf16pos_116_, v_off_117_);
lean_dec_ref(v_s_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPos(lean_object* v_s_119_, lean_object* v_pos_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = l_Lean_String_utf16PosToCodepointPosFrom(v_s_119_, v_pos_120_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_utf16PosToCodepointPos___boxed(lean_object* v_s_123_, lean_object* v_pos_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_String_utf16PosToCodepointPos(v_s_123_, v_pos_124_);
lean_dec_ref(v_s_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf8PosFrom(lean_object* v_s_126_, lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
lean_object* v_zero_129_; uint8_t v_isZero_130_; 
v_zero_129_ = lean_unsigned_to_nat(0u);
v_isZero_130_ = lean_nat_dec_eq(v_x_128_, v_zero_129_);
if (v_isZero_130_ == 1)
{
lean_dec(v_x_128_);
return v_x_127_;
}
else
{
lean_object* v_one_131_; lean_object* v_n_132_; lean_object* v___x_133_; 
v_one_131_ = lean_unsigned_to_nat(1u);
v_n_132_ = lean_nat_sub(v_x_128_, v_one_131_);
lean_dec(v_x_128_);
v___x_133_ = lean_string_utf8_next(v_s_126_, v_x_127_);
lean_dec(v_x_127_);
v_x_127_ = v___x_133_;
v_x_128_ = v_n_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_String_codepointPosToUtf8PosFrom___boxed(lean_object* v_s_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_String_codepointPosToUtf8PosFrom(v_s_135_, v_x_136_, v_x_137_);
lean_dec_ref(v_s_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(lean_object* v_text_139_, lean_object* v_line_140_){
_start:
{
lean_object* v_positions_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_positions_141_ = lean_ctor_get(v_text_139_, 1);
v___x_142_ = lean_array_get_size(v_positions_141_);
v___x_143_ = lean_nat_dec_lt(v_line_140_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_nat_dec_eq(v___x_142_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_sub(v___x_142_, v___x_146_);
v___x_148_ = lean_array_get_borrowed(v___x_144_, v_positions_141_, v___x_147_);
lean_dec(v___x_147_);
lean_inc(v___x_148_);
return v___x_148_;
}
else
{
return v___x_144_;
}
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_array_fget_borrowed(v_positions_141_, v_line_140_);
lean_inc(v___x_149_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(lean_object* v_text_150_, lean_object* v_line_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_150_, v_line_151_);
lean_dec(v_line_151_);
lean_dec_ref(v_text_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object* v_text_153_, lean_object* v_pos_154_){
_start:
{
lean_object* v_line_155_; lean_object* v_character_156_; lean_object* v_source_157_; lean_object* v_lineStartPos_158_; lean_object* v_chr_159_; lean_object* v___x_160_; 
v_line_155_ = lean_ctor_get(v_pos_154_, 0);
lean_inc(v_line_155_);
v_character_156_ = lean_ctor_get(v_pos_154_, 1);
lean_inc(v_character_156_);
lean_dec_ref(v_pos_154_);
v_source_157_ = lean_ctor_get(v_text_153_, 0);
v_lineStartPos_158_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_153_, v_line_155_);
lean_dec(v_line_155_);
lean_inc(v_lineStartPos_158_);
v_chr_159_ = l_Lean_String_utf16PosToCodepointPosFrom(v_source_157_, v_character_156_, v_lineStartPos_158_);
v___x_160_ = l_Lean_String_codepointPosToUtf8PosFrom(v_source_157_, v_lineStartPos_158_, v_chr_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspPosToUtf8Pos___boxed(lean_object* v_text_161_, lean_object* v_pos_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_161_, v_pos_162_);
lean_dec_ref(v_text_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object* v_text_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_line_166_; lean_object* v_column_167_; lean_object* v_source_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_line_166_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_line_166_);
v_column_167_ = lean_ctor_get(v_x_165_, 1);
lean_inc(v_column_167_);
lean_dec_ref(v_x_165_);
v_source_168_ = lean_ctor_get(v_text_164_, 0);
lean_inc_ref(v_source_168_);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_sub(v_line_166_, v___x_169_);
lean_dec(v_line_166_);
v___x_171_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_164_, v___x_170_);
v_isSharedCheck_179_ = !lean_is_exclusive(v_text_164_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_180_ = lean_ctor_get(v_text_164_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_text_164_, 0);
lean_dec(v_unused_181_);
v___x_173_ = v_text_164_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_dec(v_text_164_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = l_Lean_String_codepointPosToUtf16PosFrom(v_source_168_, v_column_167_, v___x_171_);
lean_dec_ref(v_source_168_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_175_);
lean_ctor_set(v___x_173_, 0, v___x_170_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object* v_text_182_, lean_object* v_pos_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_inc_ref(v_text_182_);
v___x_184_ = l_Lean_FileMap_toPosition(v_text_182_, v_pos_183_);
v___x_185_ = l_Lean_FileMap_leanPosToLspPos(v_text_182_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8PosToLspPos___boxed(lean_object* v_text_186_, lean_object* v_pos_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_FileMap_utf8PosToLspPos(v_text_186_, v_pos_187_);
lean_dec(v_pos_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object* v_text_189_, lean_object* v_range_190_){
_start:
{
lean_object* v_start_191_; lean_object* v_stop_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
v_start_191_ = lean_ctor_get(v_range_190_, 0);
v_stop_192_ = lean_ctor_get(v_range_190_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_range_190_);
if (v_isSharedCheck_201_ == 0)
{
v___x_194_ = v_range_190_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_stop_192_);
lean_inc(v_start_191_);
lean_dec(v_range_190_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
lean_inc_ref(v_text_189_);
v___x_196_ = l_Lean_FileMap_utf8PosToLspPos(v_text_189_, v_start_191_);
lean_dec(v_start_191_);
v___x_197_ = l_Lean_FileMap_utf8PosToLspPos(v_text_189_, v_stop_192_);
lean_dec(v_stop_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_197_);
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
lean_object* l_Lean_FileMap_lspRangeOfStx_x3f(lean_object* v_text_202_, lean_object* v_stx_203_, uint8_t v_canonicalOnly_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Syntax_getRange_x3f(v_stx_203_, v_canonicalOnly_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v_text_202_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_202_, v_val_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_FileMap_lspRangeOfStx_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_202_ = stack[0].m_obj;
lean_object* v_stx_203_ = stack[1].m_obj;
uint8_t v_canonicalOnly_204_ = stack[2].m_num;
lean_object* v_res_216_;
v_res_216_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_202_, v_stx_203_, v_canonicalOnly_204_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeOfStx_x3f___boxed(lean_object* v_text_217_, lean_object* v_stx_218_, lean_object* v_canonicalOnly_219_){
_start:
{
uint8_t v_canonicalOnly_boxed_220_; lean_object* v_res_221_; 
v_canonicalOnly_boxed_220_ = lean_unbox(v_canonicalOnly_219_);
v_res_221_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_217_, v_stx_218_, v_canonicalOnly_boxed_220_);
lean_dec(v_stx_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object* v_text_222_, lean_object* v_range_223_){
_start:
{
lean_object* v_start_224_; lean_object* v_end_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_234_; 
v_start_224_ = lean_ctor_get(v_range_223_, 0);
v_end_225_ = lean_ctor_get(v_range_223_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_range_223_);
if (v_isSharedCheck_234_ == 0)
{
v___x_227_ = v_range_223_;
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_end_225_);
lean_inc(v_start_224_);
lean_dec(v_range_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_229_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_222_, v_start_224_);
v___x_230_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_222_, v_end_225_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_230_);
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lspRangeToUtf8Range___boxed(lean_object* v_text_235_, lean_object* v_range_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_235_, v_range_236_);
lean_dec_ref(v_text_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofFilePositions(lean_object* v_text_238_, lean_object* v_pos_239_, lean_object* v_endPos_240_){
_start:
{
lean_object* v___x_241_; lean_object* v_character_242_; lean_object* v___x_243_; lean_object* v_character_244_; lean_object* v___x_245_; 
lean_inc_ref(v_pos_239_);
lean_inc_ref(v_text_238_);
v___x_241_ = l_Lean_FileMap_leanPosToLspPos(v_text_238_, v_pos_239_);
v_character_242_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_character_242_);
lean_dec_ref(v___x_241_);
lean_inc_ref(v_endPos_240_);
v___x_243_ = l_Lean_FileMap_leanPosToLspPos(v_text_238_, v_endPos_240_);
v_character_244_ = lean_ctor_get(v___x_243_, 1);
lean_inc(v_character_244_);
lean_dec_ref(v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_245_, 0, v_pos_239_);
lean_ctor_set(v___x_245_, 1, v_character_242_);
lean_ctor_set(v___x_245_, 2, v_endPos_240_);
lean_ctor_set(v___x_245_, 3, v_character_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object* v_text_246_, lean_object* v_pos_247_, lean_object* v_endPos_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_inc_ref_n(v_text_246_, 2);
v___x_249_ = l_Lean_FileMap_toPosition(v_text_246_, v_pos_247_);
v___x_250_ = l_Lean_FileMap_toPosition(v_text_246_, v_endPos_248_);
v___x_251_ = l_Lean_DeclarationRange_ofFilePositions(v_text_246_, v___x_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_ofStringPositions___boxed(lean_object* v_text_252_, lean_object* v_pos_253_, lean_object* v_endPos_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_DeclarationRange_ofStringPositions(v_text_252_, v_pos_253_, v_endPos_254_);
lean_dec(v_endPos_254_);
lean_dec(v_pos_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_DeclarationRange_toLspRange(lean_object* v_r_256_){
_start:
{
lean_object* v_pos_257_; lean_object* v_endPos_258_; lean_object* v_charUtf16_259_; lean_object* v_endCharUtf16_260_; lean_object* v_line_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_281_; 
v_pos_257_ = lean_ctor_get(v_r_256_, 0);
lean_inc_ref(v_pos_257_);
v_endPos_258_ = lean_ctor_get(v_r_256_, 2);
lean_inc_ref(v_endPos_258_);
v_charUtf16_259_ = lean_ctor_get(v_r_256_, 1);
lean_inc(v_charUtf16_259_);
v_endCharUtf16_260_ = lean_ctor_get(v_r_256_, 3);
lean_inc(v_endCharUtf16_260_);
lean_dec_ref(v_r_256_);
v_line_261_ = lean_ctor_get(v_pos_257_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_pos_257_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_pos_257_, 1);
lean_dec(v_unused_282_);
v___x_263_ = v_pos_257_;
v_isShared_264_ = v_isSharedCheck_281_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_line_261_);
lean_dec(v_pos_257_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_281_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_line_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_279_; 
v_line_265_ = lean_ctor_get(v_endPos_258_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_endPos_258_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_endPos_258_, 1);
lean_dec(v_unused_280_);
v___x_267_ = v_endPos_258_;
v_isShared_268_ = v_isSharedCheck_279_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_line_265_);
lean_dec(v_endPos_258_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_279_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_sub(v_line_261_, v___x_269_);
lean_dec(v_line_261_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_charUtf16_259_);
lean_ctor_set(v___x_267_, 0, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_charUtf16_259_);
v___x_272_ = v_reuseFailAlloc_278_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_nat_sub(v_line_265_, v___x_269_);
lean_dec(v_line_265_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_endCharUtf16_260_);
lean_ctor_set(v___x_263_, 0, v___x_273_);
v___x_275_ = v___x_263_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_endCharUtf16_260_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_272_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
