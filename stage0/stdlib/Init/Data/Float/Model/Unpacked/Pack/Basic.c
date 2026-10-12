// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Pack.Basic
// Imports: public import Init.Data.Float.Model.Unpacked.Basic public import Init.Data.Float.Model.Format.Basic public import Init.Data.Nat.Bitwise public import Init.Omega public import Init.Data.BitVec.Lemmas public import Init.Data.BitVec.Bootstrap
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_neg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_Sign_toBitVec(uint8_t);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_Sign_ofBitVec(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Float_Model_Format_exponentBias(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* l_Float_Model_Format_mantissaBits(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packComponents(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packComponents___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedInfinity(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedInfinity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedNaN(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedNaN___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedZero(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_pack_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_pack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_pack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackMantissa(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackMantissa___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackExponent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackExponent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackSign(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackSign___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_unpack___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_unpack___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_unpack___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_unpack___closed__1;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpack___boxed(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_packComponents(lean_object* v_spec_1_, uint8_t v_sign_2_, lean_object* v_exponent_3_, lean_object* v_mantissa_4_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_5_; lean_object* v_exponentBits_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_mantissaBitsWithoutImplicit_5_ = lean_ctor_get(v_spec_1_, 0);
v_exponentBits_6_ = lean_ctor_get(v_spec_1_, 1);
v___x_7_ = l_Float_Model_UnpackedFloat_Sign_toBitVec(v_sign_2_);
v___x_8_ = l_BitVec_append___redArg(v_exponentBits_6_, v___x_7_, v_exponent_3_);
lean_dec(v___x_7_);
v___x_9_ = l_BitVec_append___redArg(v_mantissaBitsWithoutImplicit_5_, v___x_8_, v_mantissa_4_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_packComponents_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_1_ = stack[0].m_obj;
uint8_t v_sign_2_ = stack[1].m_num;
lean_object* v_exponent_3_ = stack[2].m_obj;
lean_object* v_mantissa_4_ = stack[3].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_1_, v_sign_2_, v_exponent_3_, v_mantissa_4_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packComponents___boxed(lean_object* v_spec_11_, lean_object* v_sign_12_, lean_object* v_exponent_13_, lean_object* v_mantissa_14_){
_start:
{
uint8_t v_sign_boxed_15_; lean_object* v_res_16_; 
v_sign_boxed_15_ = lean_unbox(v_sign_12_);
v_res_16_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_11_, v_sign_boxed_15_, v_exponent_13_, v_mantissa_14_);
lean_dec(v_mantissa_14_);
lean_dec(v_exponent_13_);
lean_dec_ref(v_spec_11_);
return v_res_16_;
}
}
lean_object* l_Float_Model_UnpackedFloat_packedInfinity(lean_object* v_spec_17_, uint8_t v_sign_18_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_19_; lean_object* v_exponentBits_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_mantissaBitsWithoutImplicit_19_ = lean_ctor_get(v_spec_17_, 0);
v_exponentBits_20_ = lean_ctor_get(v_spec_17_, 1);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = l_BitVec_ofNat(v_exponentBits_20_, v___x_21_);
v___x_23_ = l_BitVec_neg(v_exponentBits_20_, v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_19_, v___x_24_);
v___x_26_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_17_, v_sign_18_, v___x_23_, v___x_25_);
lean_dec(v___x_25_);
lean_dec(v___x_23_);
return v___x_26_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_packedInfinity_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_17_ = stack[0].m_obj;
uint8_t v_sign_18_ = stack[1].m_num;
lean_object* v_res_27_;
v_res_27_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_17_, v_sign_18_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedInfinity___boxed(lean_object* v_spec_28_, lean_object* v_sign_29_){
_start:
{
uint8_t v_sign_boxed_30_; lean_object* v_res_31_; 
v_sign_boxed_30_ = lean_unbox(v_sign_29_);
v_res_31_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_28_, v_sign_boxed_30_);
lean_dec_ref(v_spec_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedNaN(lean_object* v_spec_32_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_33_; lean_object* v_exponentBits_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_mantissaBitsWithoutImplicit_33_ = lean_ctor_get(v_spec_32_, 0);
v_exponentBits_34_ = lean_ctor_get(v_spec_32_, 1);
v___x_35_ = 1;
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = l_BitVec_ofNat(v_exponentBits_34_, v___x_36_);
v___x_38_ = l_BitVec_neg(v_exponentBits_34_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_33_, v___x_36_);
v___x_40_ = lean_nat_sub(v_mantissaBitsWithoutImplicit_33_, v___x_36_);
v___x_41_ = l_BitVec_shiftLeft(v_mantissaBitsWithoutImplicit_33_, v___x_39_, v___x_40_);
lean_dec(v___x_40_);
lean_dec(v___x_39_);
v___x_42_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_32_, v___x_35_, v___x_38_, v___x_41_);
lean_dec(v___x_41_);
lean_dec(v___x_38_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedNaN___boxed(lean_object* v_spec_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Float_Model_UnpackedFloat_packedNaN(v_spec_43_);
lean_dec_ref(v_spec_43_);
return v_res_44_;
}
}
lean_object* l_Float_Model_UnpackedFloat_packedZero(lean_object* v_spec_45_, uint8_t v_sign_46_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_47_; lean_object* v_exponentBits_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_mantissaBitsWithoutImplicit_47_ = lean_ctor_get(v_spec_45_, 0);
v_exponentBits_48_ = lean_ctor_get(v_spec_45_, 1);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_BitVec_ofNat(v_exponentBits_48_, v___x_49_);
v___x_51_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_47_, v___x_49_);
v___x_52_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_45_, v_sign_46_, v___x_50_, v___x_51_);
lean_dec(v___x_51_);
lean_dec(v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_packedZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_45_ = stack[0].m_obj;
uint8_t v_sign_46_ = stack[1].m_num;
lean_object* v_res_53_;
v_res_53_ = l_Float_Model_UnpackedFloat_packedZero(v_spec_45_, v_sign_46_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedZero___boxed(lean_object* v_spec_54_, lean_object* v_sign_55_){
_start:
{
uint8_t v_sign_boxed_56_; lean_object* v_res_57_; 
v_sign_boxed_56_ = lean_unbox(v_sign_55_);
v_res_57_ = l_Float_Model_UnpackedFloat_packedZero(v_spec_54_, v_sign_boxed_56_);
lean_dec_ref(v_spec_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_pack_spec__0(lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_nat_to_int(v_a_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_pack(lean_object* v_spec_60_, lean_object* v_x_61_){
_start:
{
switch(lean_obj_tag(v_x_61_))
{
case 0:
{
uint8_t v_sign_62_; lean_object* v___x_63_; 
v_sign_62_ = lean_ctor_get_uint8(v_x_61_, 0);
v___x_63_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_60_, v_sign_62_);
lean_dec_ref(v_spec_60_);
return v___x_63_;
}
case 1:
{
lean_object* v___x_64_; 
v___x_64_ = l_Float_Model_UnpackedFloat_packedNaN(v_spec_60_);
lean_dec_ref(v_spec_60_);
return v___x_64_;
}
case 2:
{
uint8_t v_sign_65_; lean_object* v___x_66_; 
v_sign_65_ = lean_ctor_get_uint8(v_x_61_, 0);
v___x_66_ = l_Float_Model_UnpackedFloat_packedZero(v_spec_60_, v_sign_65_);
lean_dec_ref(v_spec_60_);
return v___x_66_;
}
default: 
{
uint8_t v_sign_67_; lean_object* v_mantissa_68_; lean_object* v_exponent_69_; lean_object* v_mantissaBitsWithoutImplicit_70_; lean_object* v_exponentBits_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_biasedExponent_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_sign_67_ = lean_ctor_get_uint8(v_x_61_, sizeof(void*)*2);
v_mantissa_68_ = lean_ctor_get(v_x_61_, 0);
v_exponent_69_ = lean_ctor_get(v_x_61_, 1);
v_mantissaBitsWithoutImplicit_70_ = lean_ctor_get(v_spec_60_, 0);
v_exponentBits_71_ = lean_ctor_get(v_spec_60_, 1);
v___x_72_ = l_Float_Model_Format_exponentBias(v_spec_60_);
v___x_73_ = lean_nat_to_int(v___x_72_);
v___x_74_ = lean_int_add(v_exponent_69_, v___x_73_);
lean_dec(v___x_73_);
lean_inc(v_mantissaBitsWithoutImplicit_70_);
v___x_75_ = lean_nat_to_int(v_mantissaBitsWithoutImplicit_70_);
v___x_76_ = lean_int_add(v___x_74_, v___x_75_);
lean_dec(v___x_75_);
lean_dec(v___x_74_);
v_biasedExponent_77_ = l_Int_toNat(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_pow(v___x_78_, v_exponentBits_71_);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_add(v_biasedExponent_77_, v___x_80_);
v___x_82_ = lean_nat_dec_le(v___x_79_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v___x_79_);
if (v___x_82_ == 0)
{
lean_object* v_actualMantissaBits_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_actualMantissaBits_83_ = lean_nat_log2(v_mantissa_68_);
v___x_84_ = lean_nat_add(v_actualMantissaBits_83_, v___x_80_);
lean_dec(v_actualMantissaBits_83_);
v___x_85_ = l_Float_Model_Format_mantissaBits(v_spec_60_);
v___x_86_ = lean_nat_dec_eq(v___x_84_, v___x_85_);
lean_dec(v___x_85_);
lean_dec(v___x_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_biasedExponent_77_);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_BitVec_ofNat(v_exponentBits_71_, v___x_87_);
v___x_89_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_70_, v_mantissa_68_);
v___x_90_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_60_, v_sign_67_, v___x_88_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_88_);
lean_dec_ref(v_spec_60_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = l_BitVec_ofNat(v_exponentBits_71_, v_biasedExponent_77_);
lean_dec(v_biasedExponent_77_);
v___x_92_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_70_, v_mantissa_68_);
v___x_93_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_60_, v_sign_67_, v___x_91_, v___x_92_);
lean_dec(v___x_92_);
lean_dec(v___x_91_);
lean_dec_ref(v_spec_60_);
return v___x_93_;
}
}
else
{
lean_object* v___x_94_; 
lean_dec(v_biasedExponent_77_);
v___x_94_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_60_, v_sign_67_);
lean_dec_ref(v_spec_60_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_pack___boxed(lean_object* v_spec_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Float_Model_UnpackedFloat_pack(v_spec_95_, v_x_96_);
lean_dec(v_x_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackMantissa(lean_object* v_spec_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_mantissaBitsWithoutImplicit_100_ = lean_ctor_get(v_spec_98_, 0);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_BitVec_extractLsb_x27___redArg(v___x_101_, v_mantissaBitsWithoutImplicit_100_, v_b_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackMantissa___boxed(lean_object* v_spec_103_, lean_object* v_b_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Float_Model_UnpackedFloat_unpackMantissa(v_spec_103_, v_b_104_);
lean_dec(v_b_104_);
lean_dec_ref(v_spec_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackExponent(lean_object* v_spec_106_, lean_object* v_b_107_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_108_; lean_object* v_exponentBits_109_; lean_object* v___x_110_; 
v_mantissaBitsWithoutImplicit_108_ = lean_ctor_get(v_spec_106_, 0);
v_exponentBits_109_ = lean_ctor_get(v_spec_106_, 1);
v___x_110_ = l_BitVec_extractLsb_x27___redArg(v_mantissaBitsWithoutImplicit_108_, v_exponentBits_109_, v_b_107_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackExponent___boxed(lean_object* v_spec_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Float_Model_UnpackedFloat_unpackExponent(v_spec_111_, v_b_112_);
lean_dec(v_b_112_);
lean_dec_ref(v_spec_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackSign(lean_object* v_spec_114_, lean_object* v_b_115_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_116_; lean_object* v_exponentBits_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_mantissaBitsWithoutImplicit_116_ = lean_ctor_get(v_spec_114_, 0);
v_exponentBits_117_ = lean_ctor_get(v_spec_114_, 1);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_add(v_mantissaBitsWithoutImplicit_116_, v_exponentBits_117_);
v___x_120_ = l_BitVec_extractLsb_x27___redArg(v___x_119_, v___x_118_, v_b_115_);
lean_dec(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackSign___boxed(lean_object* v_spec_121_, lean_object* v_b_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Float_Model_UnpackedFloat_unpackSign(v_spec_121_, v_b_122_);
lean_dec(v_b_122_);
lean_dec_ref(v_spec_121_);
return v_res_123_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_unpack___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = l_BitVec_ofNat(v___x_124_, v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_unpack___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpack(lean_object* v_spec_128_, lean_object* v_b_129_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_130_; lean_object* v_exponentBits_131_; lean_object* v_mantissaVec_132_; lean_object* v_exponentVec_133_; lean_object* v_signVec_134_; uint8_t v_sign_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_mantissaBitsWithoutImplicit_130_ = lean_ctor_get(v_spec_128_, 0);
lean_inc(v_mantissaBitsWithoutImplicit_130_);
v_exponentBits_131_ = lean_ctor_get(v_spec_128_, 1);
lean_inc(v_exponentBits_131_);
v_mantissaVec_132_ = l_Float_Model_UnpackedFloat_unpackMantissa(v_spec_128_, v_b_129_);
v_exponentVec_133_ = l_Float_Model_UnpackedFloat_unpackExponent(v_spec_128_, v_b_129_);
v_signVec_134_ = l_Float_Model_UnpackedFloat_unpackSign(v_spec_128_, v_b_129_);
v_sign_135_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_signVec_134_);
lean_dec(v_signVec_134_);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = l_BitVec_ofNat(v_exponentBits_131_, v___x_136_);
v___x_138_ = l_BitVec_neg(v_exponentBits_131_, v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = lean_nat_dec_eq(v_exponentVec_133_, v___x_138_);
lean_dec(v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_exponent_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
lean_inc(v_exponentVec_133_);
v___x_140_ = lean_nat_to_int(v_exponentVec_133_);
v___x_141_ = l_Float_Model_Format_exponentBias(v_spec_128_);
lean_dec_ref(v_spec_128_);
v___x_142_ = lean_nat_to_int(v___x_141_);
lean_inc(v_mantissaBitsWithoutImplicit_130_);
v___x_143_ = lean_nat_to_int(v_mantissaBitsWithoutImplicit_130_);
v___x_144_ = lean_int_add(v___x_142_, v___x_143_);
lean_dec(v___x_143_);
lean_dec(v___x_142_);
v_exponent_145_ = lean_int_sub(v___x_140_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v___x_140_);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_BitVec_ofNat(v_exponentBits_131_, v___x_146_);
lean_dec(v_exponentBits_131_);
v___x_148_ = lean_nat_dec_eq(v_exponentVec_133_, v___x_147_);
lean_dec(v___x_147_);
lean_dec(v_exponentVec_133_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Float_Model_UnpackedFloat_unpack___closed__0, &l_Float_Model_UnpackedFloat_unpack___closed__0_once, _init_l_Float_Model_UnpackedFloat_unpack___closed__0);
v___x_150_ = l_BitVec_append___redArg(v_mantissaBitsWithoutImplicit_130_, v___x_149_, v_mantissaVec_132_);
lean_dec(v_mantissaVec_132_);
lean_dec(v_mantissaBitsWithoutImplicit_130_);
v___x_151_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_exponent_145_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*2, v_sign_135_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_130_, v___x_146_);
lean_dec(v_mantissaBitsWithoutImplicit_130_);
v___x_153_ = lean_nat_dec_eq(v_mantissaVec_132_, v___x_152_);
lean_dec(v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&l_Float_Model_UnpackedFloat_unpack___closed__1, &l_Float_Model_UnpackedFloat_unpack___closed__1_once, _init_l_Float_Model_UnpackedFloat_unpack___closed__1);
v___x_155_ = lean_int_add(v_exponent_145_, v___x_154_);
lean_dec(v_exponent_145_);
v___x_156_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_156_, 0, v_mantissaVec_132_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*2, v_sign_135_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
lean_dec(v_exponent_145_);
lean_dec(v_mantissaVec_132_);
v___x_157_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_157_, 0, v_sign_135_);
return v___x_157_;
}
}
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
lean_dec(v_exponentVec_133_);
lean_dec(v_exponentBits_131_);
lean_dec_ref(v_spec_128_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_130_, v___x_158_);
lean_dec(v_mantissaBitsWithoutImplicit_130_);
v___x_160_ = lean_nat_dec_eq(v_mantissaVec_132_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v_mantissaVec_132_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(1);
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_162_, 0, v_sign_135_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpack___boxed(lean_object* v_spec_163_, lean_object* v_b_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Float_Model_UnpackedFloat_unpack(v_spec_163_, v_b_164_);
lean_dec(v_b_164_);
return v_res_165_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
