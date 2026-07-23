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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packComponents(lean_object* v_spec_1_, uint8_t v_sign_2_, lean_object* v_exponent_3_, lean_object* v_mantissa_4_){
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packComponents___boxed(lean_object* v_spec_10_, lean_object* v_sign_11_, lean_object* v_exponent_12_, lean_object* v_mantissa_13_){
_start:
{
uint8_t v_sign_boxed_14_; lean_object* v_res_15_; 
v_sign_boxed_14_ = lean_unbox(v_sign_11_);
v_res_15_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_10_, v_sign_boxed_14_, v_exponent_12_, v_mantissa_13_);
lean_dec(v_mantissa_13_);
lean_dec(v_exponent_12_);
lean_dec_ref(v_spec_10_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedInfinity(lean_object* v_spec_16_, uint8_t v_sign_17_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_18_; lean_object* v_exponentBits_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_mantissaBitsWithoutImplicit_18_ = lean_ctor_get(v_spec_16_, 0);
v_exponentBits_19_ = lean_ctor_get(v_spec_16_, 1);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_BitVec_ofNat(v_exponentBits_19_, v___x_20_);
v___x_22_ = l_BitVec_neg(v_exponentBits_19_, v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_18_, v___x_23_);
v___x_25_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_16_, v_sign_17_, v___x_22_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedInfinity___boxed(lean_object* v_spec_26_, lean_object* v_sign_27_){
_start:
{
uint8_t v_sign_boxed_28_; lean_object* v_res_29_; 
v_sign_boxed_28_ = lean_unbox(v_sign_27_);
v_res_29_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_26_, v_sign_boxed_28_);
lean_dec_ref(v_spec_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedNaN(lean_object* v_spec_30_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_31_; lean_object* v_exponentBits_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_mantissaBitsWithoutImplicit_31_ = lean_ctor_get(v_spec_30_, 0);
v_exponentBits_32_ = lean_ctor_get(v_spec_30_, 1);
v___x_33_ = 1;
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = l_BitVec_ofNat(v_exponentBits_32_, v___x_34_);
v___x_36_ = l_BitVec_neg(v_exponentBits_32_, v___x_35_);
lean_dec(v___x_35_);
v___x_37_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_31_, v___x_34_);
v___x_38_ = lean_nat_sub(v_mantissaBitsWithoutImplicit_31_, v___x_34_);
v___x_39_ = l_BitVec_shiftLeft(v_mantissaBitsWithoutImplicit_31_, v___x_37_, v___x_38_);
lean_dec(v___x_38_);
lean_dec(v___x_37_);
v___x_40_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_30_, v___x_33_, v___x_36_, v___x_39_);
lean_dec(v___x_39_);
lean_dec(v___x_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedNaN___boxed(lean_object* v_spec_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Float_Model_UnpackedFloat_packedNaN(v_spec_41_);
lean_dec_ref(v_spec_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedZero(lean_object* v_spec_43_, uint8_t v_sign_44_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_45_; lean_object* v_exponentBits_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_mantissaBitsWithoutImplicit_45_ = lean_ctor_get(v_spec_43_, 0);
v_exponentBits_46_ = lean_ctor_get(v_spec_43_, 1);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = l_BitVec_ofNat(v_exponentBits_46_, v___x_47_);
v___x_49_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_45_, v___x_47_);
v___x_50_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_43_, v_sign_44_, v___x_48_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_packedZero___boxed(lean_object* v_spec_51_, lean_object* v_sign_52_){
_start:
{
uint8_t v_sign_boxed_53_; lean_object* v_res_54_; 
v_sign_boxed_53_ = lean_unbox(v_sign_52_);
v_res_54_ = l_Float_Model_UnpackedFloat_packedZero(v_spec_51_, v_sign_boxed_53_);
lean_dec_ref(v_spec_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_pack_spec__0(lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_nat_to_int(v_a_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_pack(lean_object* v_spec_57_, lean_object* v_x_58_){
_start:
{
switch(lean_obj_tag(v_x_58_))
{
case 0:
{
uint8_t v_sign_59_; lean_object* v___x_60_; 
v_sign_59_ = lean_ctor_get_uint8(v_x_58_, 0);
v___x_60_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_57_, v_sign_59_);
lean_dec_ref(v_spec_57_);
return v___x_60_;
}
case 1:
{
lean_object* v___x_61_; 
v___x_61_ = l_Float_Model_UnpackedFloat_packedNaN(v_spec_57_);
lean_dec_ref(v_spec_57_);
return v___x_61_;
}
case 2:
{
uint8_t v_sign_62_; lean_object* v___x_63_; 
v_sign_62_ = lean_ctor_get_uint8(v_x_58_, 0);
v___x_63_ = l_Float_Model_UnpackedFloat_packedZero(v_spec_57_, v_sign_62_);
lean_dec_ref(v_spec_57_);
return v___x_63_;
}
default: 
{
uint8_t v_sign_64_; lean_object* v_mantissa_65_; lean_object* v_exponent_66_; lean_object* v_mantissaBitsWithoutImplicit_67_; lean_object* v_exponentBits_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_biasedExponent_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_sign_64_ = lean_ctor_get_uint8(v_x_58_, sizeof(void*)*2);
v_mantissa_65_ = lean_ctor_get(v_x_58_, 0);
v_exponent_66_ = lean_ctor_get(v_x_58_, 1);
v_mantissaBitsWithoutImplicit_67_ = lean_ctor_get(v_spec_57_, 0);
v_exponentBits_68_ = lean_ctor_get(v_spec_57_, 1);
v___x_69_ = l_Float_Model_Format_exponentBias(v_spec_57_);
v___x_70_ = lean_nat_to_int(v___x_69_);
v___x_71_ = lean_int_add(v_exponent_66_, v___x_70_);
lean_dec(v___x_70_);
lean_inc(v_mantissaBitsWithoutImplicit_67_);
v___x_72_ = lean_nat_to_int(v_mantissaBitsWithoutImplicit_67_);
v___x_73_ = lean_int_add(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
v_biasedExponent_74_ = l_Int_toNat(v___x_73_);
lean_dec(v___x_73_);
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_pow(v___x_75_, v_exponentBits_68_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_biasedExponent_74_, v___x_77_);
v___x_79_ = lean_nat_dec_le(v___x_76_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_76_);
if (v___x_79_ == 0)
{
lean_object* v_actualMantissaBits_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_actualMantissaBits_80_ = lean_nat_log2(v_mantissa_65_);
v___x_81_ = lean_nat_add(v_actualMantissaBits_80_, v___x_77_);
lean_dec(v_actualMantissaBits_80_);
v___x_82_ = l_Float_Model_Format_mantissaBits(v_spec_57_);
v___x_83_ = lean_nat_dec_eq(v___x_81_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_81_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_biasedExponent_74_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_BitVec_ofNat(v_exponentBits_68_, v___x_84_);
v___x_86_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_67_, v_mantissa_65_);
v___x_87_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_57_, v_sign_64_, v___x_85_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v___x_85_);
lean_dec_ref(v_spec_57_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = l_BitVec_ofNat(v_exponentBits_68_, v_biasedExponent_74_);
lean_dec(v_biasedExponent_74_);
v___x_89_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_67_, v_mantissa_65_);
v___x_90_ = l_Float_Model_UnpackedFloat_packComponents(v_spec_57_, v_sign_64_, v___x_88_, v___x_89_);
lean_dec(v___x_89_);
lean_dec(v___x_88_);
lean_dec_ref(v_spec_57_);
return v___x_90_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec(v_biasedExponent_74_);
v___x_91_ = l_Float_Model_UnpackedFloat_packedInfinity(v_spec_57_, v_sign_64_);
lean_dec_ref(v_spec_57_);
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_pack___boxed(lean_object* v_spec_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Float_Model_UnpackedFloat_pack(v_spec_92_, v_x_93_);
lean_dec(v_x_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackMantissa(lean_object* v_spec_95_, lean_object* v_b_96_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_mantissaBitsWithoutImplicit_97_ = lean_ctor_get(v_spec_95_, 0);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = l_BitVec_extractLsb_x27___redArg(v___x_98_, v_mantissaBitsWithoutImplicit_97_, v_b_96_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackMantissa___boxed(lean_object* v_spec_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Float_Model_UnpackedFloat_unpackMantissa(v_spec_100_, v_b_101_);
lean_dec(v_b_101_);
lean_dec_ref(v_spec_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackExponent(lean_object* v_spec_103_, lean_object* v_b_104_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_105_; lean_object* v_exponentBits_106_; lean_object* v___x_107_; 
v_mantissaBitsWithoutImplicit_105_ = lean_ctor_get(v_spec_103_, 0);
v_exponentBits_106_ = lean_ctor_get(v_spec_103_, 1);
v___x_107_ = l_BitVec_extractLsb_x27___redArg(v_mantissaBitsWithoutImplicit_105_, v_exponentBits_106_, v_b_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackExponent___boxed(lean_object* v_spec_108_, lean_object* v_b_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Float_Model_UnpackedFloat_unpackExponent(v_spec_108_, v_b_109_);
lean_dec(v_b_109_);
lean_dec_ref(v_spec_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackSign(lean_object* v_spec_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_113_; lean_object* v_exponentBits_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_mantissaBitsWithoutImplicit_113_ = lean_ctor_get(v_spec_111_, 0);
v_exponentBits_114_ = lean_ctor_get(v_spec_111_, 1);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_mantissaBitsWithoutImplicit_113_, v_exponentBits_114_);
v___x_117_ = l_BitVec_extractLsb_x27___redArg(v___x_116_, v___x_115_, v_b_112_);
lean_dec(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpackSign___boxed(lean_object* v_spec_118_, lean_object* v_b_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Float_Model_UnpackedFloat_unpackSign(v_spec_118_, v_b_119_);
lean_dec(v_b_119_);
lean_dec_ref(v_spec_118_);
return v_res_120_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_unpack___closed__0(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = l_BitVec_ofNat(v___x_121_, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_unpack___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_to_int(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpack(lean_object* v_spec_125_, lean_object* v_b_126_){
_start:
{
lean_object* v_mantissaBitsWithoutImplicit_127_; lean_object* v_exponentBits_128_; lean_object* v_mantissaVec_129_; lean_object* v_exponentVec_130_; lean_object* v_signVec_131_; uint8_t v_sign_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_mantissaBitsWithoutImplicit_127_ = lean_ctor_get(v_spec_125_, 0);
lean_inc(v_mantissaBitsWithoutImplicit_127_);
v_exponentBits_128_ = lean_ctor_get(v_spec_125_, 1);
lean_inc(v_exponentBits_128_);
v_mantissaVec_129_ = l_Float_Model_UnpackedFloat_unpackMantissa(v_spec_125_, v_b_126_);
v_exponentVec_130_ = l_Float_Model_UnpackedFloat_unpackExponent(v_spec_125_, v_b_126_);
v_signVec_131_ = l_Float_Model_UnpackedFloat_unpackSign(v_spec_125_, v_b_126_);
v_sign_132_ = l_Float_Model_UnpackedFloat_Sign_ofBitVec(v_signVec_131_);
lean_dec(v_signVec_131_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = l_BitVec_ofNat(v_exponentBits_128_, v___x_133_);
v___x_135_ = l_BitVec_neg(v_exponentBits_128_, v___x_134_);
lean_dec(v___x_134_);
v___x_136_ = lean_nat_dec_eq(v_exponentVec_130_, v___x_135_);
lean_dec(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_exponent_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
lean_inc(v_exponentVec_130_);
v___x_137_ = lean_nat_to_int(v_exponentVec_130_);
v___x_138_ = l_Float_Model_Format_exponentBias(v_spec_125_);
lean_dec_ref(v_spec_125_);
v___x_139_ = lean_nat_to_int(v___x_138_);
lean_inc(v_mantissaBitsWithoutImplicit_127_);
v___x_140_ = lean_nat_to_int(v_mantissaBitsWithoutImplicit_127_);
v___x_141_ = lean_int_add(v___x_139_, v___x_140_);
lean_dec(v___x_140_);
lean_dec(v___x_139_);
v_exponent_142_ = lean_int_sub(v___x_137_, v___x_141_);
lean_dec(v___x_141_);
lean_dec(v___x_137_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = l_BitVec_ofNat(v_exponentBits_128_, v___x_143_);
lean_dec(v_exponentBits_128_);
v___x_145_ = lean_nat_dec_eq(v_exponentVec_130_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v_exponentVec_130_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&l_Float_Model_UnpackedFloat_unpack___closed__0, &l_Float_Model_UnpackedFloat_unpack___closed__0_once, _init_l_Float_Model_UnpackedFloat_unpack___closed__0);
v___x_147_ = l_BitVec_append___redArg(v_mantissaBitsWithoutImplicit_127_, v___x_146_, v_mantissaVec_129_);
lean_dec(v_mantissaVec_129_);
lean_dec(v_mantissaBitsWithoutImplicit_127_);
v___x_148_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_exponent_142_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*2, v_sign_132_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_127_, v___x_143_);
lean_dec(v_mantissaBitsWithoutImplicit_127_);
v___x_150_ = lean_nat_dec_eq(v_mantissaVec_129_, v___x_149_);
lean_dec(v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&l_Float_Model_UnpackedFloat_unpack___closed__1, &l_Float_Model_UnpackedFloat_unpack___closed__1_once, _init_l_Float_Model_UnpackedFloat_unpack___closed__1);
v___x_152_ = lean_int_add(v_exponent_142_, v___x_151_);
lean_dec(v_exponent_142_);
v___x_153_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_153_, 0, v_mantissaVec_129_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*2, v_sign_132_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
lean_dec(v_exponent_142_);
lean_dec(v_mantissaVec_129_);
v___x_154_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_154_, 0, v_sign_132_);
return v___x_154_;
}
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
lean_dec(v_exponentVec_130_);
lean_dec(v_exponentBits_128_);
lean_dec_ref(v_spec_125_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_BitVec_ofNat(v_mantissaBitsWithoutImplicit_127_, v___x_155_);
lean_dec(v_mantissaBitsWithoutImplicit_127_);
v___x_157_ = lean_nat_dec_eq(v_mantissaVec_129_, v___x_156_);
lean_dec(v___x_156_);
lean_dec(v_mantissaVec_129_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(1);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_159_, 0, v_sign_132_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_unpack___boxed(lean_object* v_spec_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Float_Model_UnpackedFloat_unpack(v_spec_160_, v_b_161_);
lean_dec(v_b_161_);
return v_res_162_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
