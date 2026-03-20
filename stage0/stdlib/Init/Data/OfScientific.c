// Lean compiler output
// Module: Init.Data.OfScientific
// Imports: public import Init.Data.Float32 import Init.Data.Nat.Log2 import Init.Meta
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
float lean_uint64_to_float32(uint64_t);
float lean_float32_scaleb(float, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
double lean_uint64_to_float(uint64_t);
double lean_float_scaleb(double, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
double lean_float_negate(double);
float lean_float32_negate(float);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_ofBinaryScientific_spec__0(lean_object*);
LEAN_EXPORT double l_Float_ofBinaryScientific(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_ofBinaryScientific___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Float_ofScientific___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_ofScientific___closed__0;
static lean_once_cell_t l_Float_ofScientific___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_ofScientific___closed__1;
LEAN_EXPORT double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Float_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instOfScientificFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOfScientificFloat___closed__0 = (const lean_object*)&l_instOfScientificFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instOfScientificFloat = (const lean_object*)&l_instOfScientificFloat___closed__0_value;
LEAN_EXPORT double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Float_ofNat___boxed(lean_object*);
static lean_once_cell_t l_Float_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_ofInt___closed__0;
LEAN_EXPORT double l_Float_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Float_ofInt___boxed(lean_object*);
LEAN_EXPORT double l_instOfNatFloat(lean_object*);
LEAN_EXPORT lean_object* l_instOfNatFloat___boxed(lean_object*);
LEAN_EXPORT double l_Nat_toFloat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toFloat___boxed(lean_object*);
LEAN_EXPORT float l_Float32_ofBinaryScientific(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofBinaryScientific___boxed(lean_object*, lean_object*);
LEAN_EXPORT float l_Float32_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instOfScientificFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOfScientificFloat32___closed__0 = (const lean_object*)&l_instOfScientificFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instOfScientificFloat32 = (const lean_object*)&l_instOfScientificFloat32___closed__0_value;
LEAN_EXPORT float lean_float32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofNat___boxed(lean_object*);
LEAN_EXPORT float l_Float32_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofInt___boxed(lean_object*);
LEAN_EXPORT float l_instOfNatFloat32(lean_object*);
LEAN_EXPORT lean_object* l_instOfNatFloat32___boxed(lean_object*);
LEAN_EXPORT float l_Nat_toFloat32(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toFloat32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_ofBinaryScientific_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT double l_Float_ofBinaryScientific(lean_object* v_m_3_, lean_object* v_e_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v_s_7_; lean_object* v___x_8_; uint64_t v_m_9_; lean_object* v___x_10_; lean_object* v_e_11_; double v___x_12_; double v___x_13_; 
v___x_5_ = lean_nat_log2(v_m_3_);
v___x_6_ = lean_unsigned_to_nat(63u);
v_s_7_ = lean_nat_sub(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v___x_8_ = lean_nat_shiftr(v_m_3_, v_s_7_);
v_m_9_ = lean_uint64_of_nat(v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lean_nat_to_int(v_s_7_);
v_e_11_ = lean_int_add(v_e_4_, v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = lean_uint64_to_float(v_m_9_);
v___x_13_ = lean_float_scaleb(v___x_12_, v_e_11_);
lean_dec(v_e_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Float_ofBinaryScientific___boxed(lean_object* v_m_14_, lean_object* v_e_15_){
_start:
{
double v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Float_ofBinaryScientific(v_m_14_, v_e_15_);
lean_dec(v_e_15_);
lean_dec(v_m_14_);
v_r_17_ = lean_box_float(v_res_16_);
return v_r_17_;
}
}
static lean_object* _init_l_Float_ofScientific___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(4u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Float_ofScientific___closed__1(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_Float_ofScientific___closed__0, &l_Float_ofScientific___closed__0_once, _init_l_Float_ofScientific___closed__0);
v___x_21_ = lean_int_neg(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT double l_Float_ofScientific(lean_object* v_m_22_, uint8_t v_s_23_, lean_object* v_e_24_){
_start:
{
if (v_s_23_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; double v___x_29_; 
v___x_25_ = lean_unsigned_to_nat(5u);
v___x_26_ = lean_nat_pow(v___x_25_, v_e_24_);
v___x_27_ = lean_nat_mul(v_m_22_, v___x_26_);
lean_dec(v___x_26_);
v___x_28_ = lean_nat_to_int(v_e_24_);
v___x_29_ = l_Float_ofBinaryScientific(v___x_27_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_27_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_s_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v_m_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; double v___x_45_; 
v___x_30_ = lean_unsigned_to_nat(64u);
v___x_31_ = lean_nat_log2(v_m_22_);
v_s_32_ = lean_nat_sub(v___x_30_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_unsigned_to_nat(3u);
v___x_34_ = lean_nat_mul(v___x_33_, v_e_24_);
v___x_35_ = lean_nat_add(v___x_34_, v_s_32_);
lean_dec(v___x_34_);
v___x_36_ = lean_nat_shiftl(v_m_22_, v___x_35_);
lean_dec(v___x_35_);
v___x_37_ = lean_unsigned_to_nat(5u);
v___x_38_ = lean_nat_pow(v___x_37_, v_e_24_);
v_m_39_ = lean_nat_div(v___x_36_, v___x_38_);
lean_dec(v___x_38_);
lean_dec(v___x_36_);
v___x_40_ = lean_obj_once(&l_Float_ofScientific___closed__1, &l_Float_ofScientific___closed__1_once, _init_l_Float_ofScientific___closed__1);
v___x_41_ = lean_nat_to_int(v_e_24_);
v___x_42_ = lean_int_mul(v___x_40_, v___x_41_);
lean_dec(v___x_41_);
v___x_43_ = lean_nat_to_int(v_s_32_);
v___x_44_ = lean_int_sub(v___x_42_, v___x_43_);
lean_dec(v___x_43_);
lean_dec(v___x_42_);
v___x_45_ = l_Float_ofBinaryScientific(v_m_39_, v___x_44_);
lean_dec(v___x_44_);
lean_dec(v_m_39_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Float_ofScientific___boxed(lean_object* v_m_46_, lean_object* v_s_47_, lean_object* v_e_48_){
_start:
{
uint8_t v_s_boxed_49_; double v_res_50_; lean_object* v_r_51_; 
v_s_boxed_49_ = lean_unbox(v_s_47_);
v_res_50_ = l_Float_ofScientific(v_m_46_, v_s_boxed_49_, v_e_48_);
lean_dec(v_m_46_);
v_r_51_ = lean_box_float(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT double lean_float_of_nat(lean_object* v_n_54_){
_start:
{
uint8_t v___x_55_; lean_object* v___x_56_; double v___x_57_; 
v___x_55_ = 0;
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_Float_ofScientific(v_n_54_, v___x_55_, v___x_56_);
lean_dec(v_n_54_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Float_ofNat___boxed(lean_object* v_n_58_){
_start:
{
double v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lean_float_of_nat(v_n_58_);
v_r_60_ = lean_box_float(v_res_59_);
return v_r_60_;
}
}
static lean_object* _init_l_Float_ofInt___closed__0(void){
_start:
{
lean_object* v_natZero_61_; lean_object* v_intZero_62_; 
v_natZero_61_ = lean_unsigned_to_nat(0u);
v_intZero_62_ = lean_nat_to_int(v_natZero_61_);
return v_intZero_62_;
}
}
LEAN_EXPORT double l_Float_ofInt(lean_object* v_x_63_){
_start:
{
lean_object* v_intZero_64_; uint8_t v_isNeg_65_; 
v_intZero_64_ = lean_obj_once(&l_Float_ofInt___closed__0, &l_Float_ofInt___closed__0_once, _init_l_Float_ofInt___closed__0);
v_isNeg_65_ = lean_int_dec_lt(v_x_63_, v_intZero_64_);
if (v_isNeg_65_ == 0)
{
lean_object* v_a_66_; double v___x_67_; 
v_a_66_ = lean_nat_abs(v_x_63_);
v___x_67_ = lean_float_of_nat(v_a_66_);
return v___x_67_;
}
else
{
lean_object* v_abs_68_; lean_object* v_one_69_; lean_object* v_a_70_; lean_object* v___x_71_; double v___x_72_; double v___x_73_; 
v_abs_68_ = lean_nat_abs(v_x_63_);
v_one_69_ = lean_unsigned_to_nat(1u);
v_a_70_ = lean_nat_sub(v_abs_68_, v_one_69_);
lean_dec(v_abs_68_);
v___x_71_ = lean_nat_add(v_a_70_, v_one_69_);
lean_dec(v_a_70_);
v___x_72_ = lean_float_of_nat(v___x_71_);
v___x_73_ = lean_float_negate(v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Float_ofInt___boxed(lean_object* v_x_74_){
_start:
{
double v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Float_ofInt(v_x_74_);
lean_dec(v_x_74_);
v_r_76_ = lean_box_float(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT double l_instOfNatFloat(lean_object* v_n_77_){
_start:
{
double v___x_78_; 
v___x_78_ = lean_float_of_nat(v_n_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_instOfNatFloat___boxed(lean_object* v_n_79_){
_start:
{
double v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_instOfNatFloat(v_n_79_);
v_r_81_ = lean_box_float(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT double l_Nat_toFloat(lean_object* v_n_82_){
_start:
{
double v___x_83_; 
v___x_83_ = lean_float_of_nat(v_n_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Nat_toFloat___boxed(lean_object* v_n_84_){
_start:
{
double v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Nat_toFloat(v_n_84_);
v_r_86_ = lean_box_float(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT float l_Float32_ofBinaryScientific(lean_object* v_m_87_, lean_object* v_e_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_s_91_; lean_object* v___x_92_; uint64_t v_m_93_; lean_object* v___x_94_; lean_object* v_e_95_; float v___x_96_; float v___x_97_; 
v___x_89_ = lean_nat_log2(v_m_87_);
v___x_90_ = lean_unsigned_to_nat(63u);
v_s_91_ = lean_nat_sub(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_nat_shiftr(v_m_87_, v_s_91_);
v_m_93_ = lean_uint64_of_nat(v___x_92_);
lean_dec(v___x_92_);
v___x_94_ = lean_nat_to_int(v_s_91_);
v_e_95_ = lean_int_add(v_e_88_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_uint64_to_float32(v_m_93_);
v___x_97_ = lean_float32_scaleb(v___x_96_, v_e_95_);
lean_dec(v_e_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofBinaryScientific___boxed(lean_object* v_m_98_, lean_object* v_e_99_){
_start:
{
float v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Float32_ofBinaryScientific(v_m_98_, v_e_99_);
lean_dec(v_e_99_);
lean_dec(v_m_98_);
v_r_101_ = lean_box_float32(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT float l_Float32_ofScientific(lean_object* v_m_102_, uint8_t v_s_103_, lean_object* v_e_104_){
_start:
{
if (v_s_103_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; float v___x_109_; 
v___x_105_ = lean_unsigned_to_nat(5u);
v___x_106_ = lean_nat_pow(v___x_105_, v_e_104_);
v___x_107_ = lean_nat_mul(v_m_102_, v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = lean_nat_to_int(v_e_104_);
v___x_109_ = l_Float32_ofBinaryScientific(v___x_107_, v___x_108_);
lean_dec(v___x_108_);
lean_dec(v___x_107_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_s_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_m_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; float v___x_125_; 
v___x_110_ = lean_unsigned_to_nat(64u);
v___x_111_ = lean_nat_log2(v_m_102_);
v_s_112_ = lean_nat_sub(v___x_110_, v___x_111_);
lean_dec(v___x_111_);
v___x_113_ = lean_unsigned_to_nat(3u);
v___x_114_ = lean_nat_mul(v___x_113_, v_e_104_);
v___x_115_ = lean_nat_add(v___x_114_, v_s_112_);
lean_dec(v___x_114_);
v___x_116_ = lean_nat_shiftl(v_m_102_, v___x_115_);
lean_dec(v___x_115_);
v___x_117_ = lean_unsigned_to_nat(5u);
v___x_118_ = lean_nat_pow(v___x_117_, v_e_104_);
v_m_119_ = lean_nat_div(v___x_116_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_116_);
v___x_120_ = lean_obj_once(&l_Float_ofScientific___closed__1, &l_Float_ofScientific___closed__1_once, _init_l_Float_ofScientific___closed__1);
v___x_121_ = lean_nat_to_int(v_e_104_);
v___x_122_ = lean_int_mul(v___x_120_, v___x_121_);
lean_dec(v___x_121_);
v___x_123_ = lean_nat_to_int(v_s_112_);
v___x_124_ = lean_int_sub(v___x_122_, v___x_123_);
lean_dec(v___x_123_);
lean_dec(v___x_122_);
v___x_125_ = l_Float32_ofBinaryScientific(v_m_119_, v___x_124_);
lean_dec(v___x_124_);
lean_dec(v_m_119_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_ofScientific___boxed(lean_object* v_m_126_, lean_object* v_s_127_, lean_object* v_e_128_){
_start:
{
uint8_t v_s_boxed_129_; float v_res_130_; lean_object* v_r_131_; 
v_s_boxed_129_ = lean_unbox(v_s_127_);
v_res_130_ = l_Float32_ofScientific(v_m_126_, v_s_boxed_129_, v_e_128_);
lean_dec(v_m_126_);
v_r_131_ = lean_box_float32(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT float lean_float32_of_nat(lean_object* v_n_134_){
_start:
{
uint8_t v___x_135_; lean_object* v___x_136_; float v___x_137_; 
v___x_135_ = 0;
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Float32_ofScientific(v_n_134_, v___x_135_, v___x_136_);
lean_dec(v_n_134_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofNat___boxed(lean_object* v_n_138_){
_start:
{
float v_res_139_; lean_object* v_r_140_; 
v_res_139_ = lean_float32_of_nat(v_n_138_);
v_r_140_ = lean_box_float32(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT float l_Float32_ofInt(lean_object* v_x_141_){
_start:
{
lean_object* v_intZero_142_; uint8_t v_isNeg_143_; 
v_intZero_142_ = lean_obj_once(&l_Float_ofInt___closed__0, &l_Float_ofInt___closed__0_once, _init_l_Float_ofInt___closed__0);
v_isNeg_143_ = lean_int_dec_lt(v_x_141_, v_intZero_142_);
if (v_isNeg_143_ == 0)
{
lean_object* v_a_144_; float v___x_145_; 
v_a_144_ = lean_nat_abs(v_x_141_);
v___x_145_ = lean_float32_of_nat(v_a_144_);
return v___x_145_;
}
else
{
lean_object* v_abs_146_; lean_object* v_one_147_; lean_object* v_a_148_; lean_object* v___x_149_; float v___x_150_; float v___x_151_; 
v_abs_146_ = lean_nat_abs(v_x_141_);
v_one_147_ = lean_unsigned_to_nat(1u);
v_a_148_ = lean_nat_sub(v_abs_146_, v_one_147_);
lean_dec(v_abs_146_);
v___x_149_ = lean_nat_add(v_a_148_, v_one_147_);
lean_dec(v_a_148_);
v___x_150_ = lean_float32_of_nat(v___x_149_);
v___x_151_ = lean_float32_negate(v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_ofInt___boxed(lean_object* v_x_152_){
_start:
{
float v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Float32_ofInt(v_x_152_);
lean_dec(v_x_152_);
v_r_154_ = lean_box_float32(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT float l_instOfNatFloat32(lean_object* v_n_155_){
_start:
{
float v___x_156_; 
v___x_156_ = lean_float32_of_nat(v_n_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_instOfNatFloat32___boxed(lean_object* v_n_157_){
_start:
{
float v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_instOfNatFloat32(v_n_157_);
v_r_159_ = lean_box_float32(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT float l_Nat_toFloat32(lean_object* v_n_160_){
_start:
{
float v___x_161_; 
v___x_161_ = lean_float32_of_nat(v_n_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Nat_toFloat32___boxed(lean_object* v_n_162_){
_start:
{
float v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Nat_toFloat32(v_n_162_);
v_r_164_ = lean_box_float32(v_res_163_);
return v_r_164_;
}
}
lean_object* runtime_initialize_Init_Data_Float32(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float32(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_OfScientific(builtin);
}
#ifdef __cplusplus
}
#endif
