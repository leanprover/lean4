// Lean compiler output
// Module: Init.Data.UInt.Modular
// Imports: public import Init.Data.UInt.Basic public import Init.Data.Nat.Gcd import Init.Data.UInt.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Nat.Mod import Init.ByCases import Init.Omega import Init.WFTactics
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_uint64_mod(uint64_t, uint64_t);
uint64_t lean_uint64_div(uint64_t, uint64_t);
uint8_t lean_uint64_dec_le(uint64_t, uint64_t);
uint64_t lean_uint64_sub(uint64_t, uint64_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint64_t lean_uint64_mul_mod(uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_mulMod___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod(uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powModWord(uint64_t, uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModWord___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_powModChunk(uint64_t, lean_object*, uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModChunk___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powModImpl_go(uint64_t, uint64_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_powModImpl(uint64_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_powModImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_invModImpl(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_invModImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg(lean_object*, uint64_t, uint64_t, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter(lean_object*, lean_object*, uint64_t, uint64_t, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_mulMod___boxed(lean_object* v_a_4_, lean_object* v_b_5_, lean_object* v_modulus_6_){
_start:
{
uint64_t v_a_boxed_7_; uint64_t v_b_boxed_8_; uint64_t v_modulus_boxed_9_; uint64_t v_res_10_; lean_object* v_r_11_; 
v_a_boxed_7_ = lean_unbox_uint64(v_a_4_);
lean_dec_ref(v_a_4_);
v_b_boxed_8_ = lean_unbox_uint64(v_b_5_);
lean_dec_ref(v_b_5_);
v_modulus_boxed_9_ = lean_unbox_uint64(v_modulus_6_);
lean_dec_ref(v_modulus_6_);
v_res_10_ = lean_uint64_mul_mod(v_a_boxed_7_, v_b_boxed_8_, v_modulus_boxed_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_cstr_to_nat("18446744073709551616");
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod(uint64_t v_modulus_13_){
_start:
{
uint64_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 0ULL;
v___x_15_ = lean_uint64_dec_eq(v_modulus_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
v___x_16_ = lean_uint64_to_nat(v_modulus_13_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0, &l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0_once, _init_l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___boxed(lean_object* v_modulus_18_){
_start:
{
uint64_t v_modulus_boxed_19_; lean_object* v_res_20_; 
v_modulus_boxed_19_ = lean_unbox_uint64(v_modulus_18_);
lean_dec_ref(v_modulus_18_);
v_res_20_ = l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod(v_modulus_boxed_19_);
return v_res_20_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powModWord(uint64_t v_base_21_, uint64_t v_exponent_22_, uint64_t v_modulus_23_, uint64_t v_result_24_){
_start:
{
uint64_t v___x_25_; uint64_t v___y_27_; uint8_t v___x_33_; 
v___x_25_ = 0ULL;
v___x_33_ = lean_uint64_dec_eq(v_exponent_22_, v___x_25_);
if (v___x_33_ == 0)
{
uint64_t v___x_34_; uint64_t v___x_35_; uint64_t v___x_36_; uint8_t v___x_37_; 
v___x_34_ = 2ULL;
v___x_35_ = lean_uint64_mod(v_exponent_22_, v___x_34_);
v___x_36_ = 1ULL;
v___x_37_ = lean_uint64_dec_eq(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
v___y_27_ = v_result_24_;
goto v___jp_26_;
}
else
{
uint64_t v___x_38_; 
v___x_38_ = lean_uint64_mul_mod(v_result_24_, v_base_21_, v_modulus_23_);
v___y_27_ = v___x_38_;
goto v___jp_26_;
}
}
else
{
return v_result_24_;
}
v___jp_26_:
{
uint64_t v___x_28_; uint64_t v_exponent_x27_29_; uint8_t v___x_30_; 
v___x_28_ = 1ULL;
v_exponent_x27_29_ = lean_uint64_shift_right(v_exponent_22_, v___x_28_);
v___x_30_ = lean_uint64_dec_eq(v_exponent_x27_29_, v___x_25_);
if (v___x_30_ == 0)
{
uint64_t v___x_31_; 
v___x_31_ = lean_uint64_mul_mod(v_base_21_, v_base_21_, v_modulus_23_);
v_base_21_ = v___x_31_;
v_exponent_22_ = v_exponent_x27_29_;
v_result_24_ = v___y_27_;
goto _start;
}
else
{
return v___y_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModWord___boxed(lean_object* v_base_39_, lean_object* v_exponent_40_, lean_object* v_modulus_41_, lean_object* v_result_42_){
_start:
{
uint64_t v_base_boxed_43_; uint64_t v_exponent_boxed_44_; uint64_t v_modulus_boxed_45_; uint64_t v_result_boxed_46_; uint64_t v_res_47_; lean_object* v_r_48_; 
v_base_boxed_43_ = lean_unbox_uint64(v_base_39_);
lean_dec_ref(v_base_39_);
v_exponent_boxed_44_ = lean_unbox_uint64(v_exponent_40_);
lean_dec_ref(v_exponent_40_);
v_modulus_boxed_45_ = lean_unbox_uint64(v_modulus_41_);
lean_dec_ref(v_modulus_41_);
v_result_boxed_46_ = lean_unbox_uint64(v_result_42_);
lean_dec_ref(v_result_42_);
v_res_47_ = l_UInt64_powModWord(v_base_boxed_43_, v_exponent_boxed_44_, v_modulus_boxed_45_, v_result_boxed_46_);
v_r_48_ = lean_box_uint64(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_UInt64_powModChunk(uint64_t v_modulus_49_, lean_object* v_x_50_, uint64_t v_x_51_, uint64_t v_x_52_, uint64_t v_x_53_){
_start:
{
lean_object* v_zero_54_; uint8_t v_isZero_55_; 
v_zero_54_ = lean_unsigned_to_nat(0u);
v_isZero_55_ = lean_nat_dec_eq(v_x_50_, v_zero_54_);
if (v_isZero_55_ == 1)
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_x_50_);
v___x_56_ = lean_box_uint64(v_x_51_);
v___x_57_ = lean_box_uint64(v_x_53_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_one_59_; lean_object* v_n_60_; uint64_t v___y_62_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint8_t v___x_70_; 
v_one_59_ = lean_unsigned_to_nat(1u);
v_n_60_ = lean_nat_sub(v_x_50_, v_one_59_);
lean_dec(v_x_50_);
v___x_67_ = 2ULL;
v___x_68_ = lean_uint64_mod(v_x_52_, v___x_67_);
v___x_69_ = 1ULL;
v___x_70_ = lean_uint64_dec_eq(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
v___y_62_ = v_x_53_;
goto v___jp_61_;
}
else
{
uint64_t v___x_71_; 
v___x_71_ = lean_uint64_mul_mod(v_x_53_, v_x_51_, v_modulus_49_);
v___y_62_ = v___x_71_;
goto v___jp_61_;
}
v___jp_61_:
{
uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; 
v___x_63_ = lean_uint64_mul_mod(v_x_51_, v_x_51_, v_modulus_49_);
v___x_64_ = 1ULL;
v___x_65_ = lean_uint64_shift_right(v_x_52_, v___x_64_);
v_x_50_ = v_n_60_;
v_x_51_ = v___x_63_;
v_x_52_ = v___x_65_;
v_x_53_ = v___y_62_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModChunk___boxed(lean_object* v_modulus_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint64_t v_modulus_boxed_77_; uint64_t v_x_79__boxed_78_; uint64_t v_x_80__boxed_79_; uint64_t v_x_81__boxed_80_; lean_object* v_res_81_; 
v_modulus_boxed_77_ = lean_unbox_uint64(v_modulus_72_);
lean_dec_ref(v_modulus_72_);
v_x_79__boxed_78_ = lean_unbox_uint64(v_x_74_);
lean_dec_ref(v_x_74_);
v_x_80__boxed_79_ = lean_unbox_uint64(v_x_75_);
lean_dec_ref(v_x_75_);
v_x_81__boxed_80_ = lean_unbox_uint64(v_x_76_);
lean_dec_ref(v_x_76_);
v_res_81_ = l_UInt64_powModChunk(v_modulus_boxed_77_, v_x_73_, v_x_79__boxed_78_, v_x_80__boxed_79_, v_x_81__boxed_80_);
return v_res_81_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powModImpl_go(uint64_t v_modulus_82_, uint64_t v_base_83_, lean_object* v_exponent_84_, uint64_t v_result_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_obj_once(&l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0, &l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0_once, _init_l___private_Init_Data_UInt_Modular_0__UInt64_wrapMod___closed__0);
v___x_87_ = lean_nat_dec_lt(v_exponent_84_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint64_t v___x_89_; lean_object* v___x_90_; lean_object* v_fst_91_; lean_object* v_snd_92_; lean_object* v___x_93_; uint64_t v___x_94_; uint64_t v___x_95_; 
v___x_88_ = lean_unsigned_to_nat(64u);
v___x_89_ = lean_uint64_of_nat(v_exponent_84_);
v___x_90_ = l_UInt64_powModChunk(v_modulus_82_, v___x_88_, v_base_83_, v___x_89_, v_result_85_);
v_fst_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_fst_91_);
v_snd_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc(v_snd_92_);
lean_dec_ref(v___x_90_);
v___x_93_ = lean_nat_shiftr(v_exponent_84_, v___x_88_);
lean_dec(v_exponent_84_);
v___x_94_ = lean_unbox_uint64(v_fst_91_);
lean_dec(v_fst_91_);
v___x_95_ = lean_unbox_uint64(v_snd_92_);
lean_dec(v_snd_92_);
v_base_83_ = v___x_94_;
v_exponent_84_ = v___x_93_;
v_result_85_ = v___x_95_;
goto _start;
}
else
{
uint64_t v___x_97_; uint64_t v___x_98_; 
v___x_97_ = lean_uint64_of_nat(v_exponent_84_);
lean_dec(v_exponent_84_);
v___x_98_ = l_UInt64_powModWord(v_base_83_, v___x_97_, v_modulus_82_, v_result_85_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModImpl_go___boxed(lean_object* v_modulus_99_, lean_object* v_base_100_, lean_object* v_exponent_101_, lean_object* v_result_102_){
_start:
{
uint64_t v_modulus_boxed_103_; uint64_t v_base_boxed_104_; uint64_t v_result_boxed_105_; uint64_t v_res_106_; lean_object* v_r_107_; 
v_modulus_boxed_103_ = lean_unbox_uint64(v_modulus_99_);
lean_dec_ref(v_modulus_99_);
v_base_boxed_104_ = lean_unbox_uint64(v_base_100_);
lean_dec_ref(v_base_100_);
v_result_boxed_105_ = lean_unbox_uint64(v_result_102_);
lean_dec_ref(v_result_102_);
v_res_106_ = l_UInt64_powModImpl_go(v_modulus_boxed_103_, v_base_boxed_104_, v_exponent_101_, v_result_boxed_105_);
v_r_107_ = lean_box_uint64(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter___redArg(lean_object* v_x_108_, lean_object* v_h__1_109_){
_start:
{
lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v___x_112_; 
v_fst_110_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_fst_110_);
v_snd_111_ = lean_ctor_get(v_x_108_, 1);
lean_inc(v_snd_111_);
lean_dec_ref(v_x_108_);
v___x_112_ = lean_apply_2(v_h__1_109_, v_fst_110_, v_snd_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModImpl_go_match__1_splitter(lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_){
_start:
{
lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_118_; 
v_fst_116_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_fst_116_);
v_snd_117_ = lean_ctor_get(v_x_114_, 1);
lean_inc(v_snd_117_);
lean_dec_ref(v_x_114_);
v___x_118_ = lean_apply_2(v_h__1_115_, v_fst_116_, v_snd_117_);
return v___x_118_;
}
}
LEAN_EXPORT uint64_t l_UInt64_powModImpl(uint64_t v_base_119_, lean_object* v_exponent_120_, uint64_t v_modulus_121_){
_start:
{
uint64_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 1ULL;
v___x_123_ = lean_uint64_dec_eq(v_modulus_121_, v___x_122_);
if (v___x_123_ == 0)
{
uint64_t v___x_124_; 
v___x_124_ = l_UInt64_powModImpl_go(v_modulus_121_, v_base_119_, v_exponent_120_, v___x_122_);
return v___x_124_;
}
else
{
uint64_t v___x_125_; 
lean_dec(v_exponent_120_);
v___x_125_ = 0ULL;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_powModImpl___boxed(lean_object* v_base_126_, lean_object* v_exponent_127_, lean_object* v_modulus_128_){
_start:
{
uint64_t v_base_boxed_129_; uint64_t v_modulus_boxed_130_; uint64_t v_res_131_; lean_object* v_r_132_; 
v_base_boxed_129_ = lean_unbox_uint64(v_base_126_);
lean_dec_ref(v_base_126_);
v_modulus_boxed_130_ = lean_unbox_uint64(v_modulus_128_);
lean_dec_ref(v_modulus_128_);
v_res_131_ = l_UInt64_powModImpl(v_base_boxed_129_, v_exponent_127_, v_modulus_boxed_130_);
v_r_132_ = lean_box_uint64(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go(uint64_t v_modulus_133_, uint64_t v_oldR_134_, uint64_t v_r_135_, uint64_t v_oldS_136_, uint64_t v_s_137_){
_start:
{
uint64_t v___y_139_; uint64_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 0ULL;
v___x_143_ = lean_uint64_dec_eq(v_r_135_, v___x_142_);
if (v___x_143_ == 0)
{
uint64_t v___x_144_; uint64_t v_product_145_; uint8_t v___x_146_; 
v___x_144_ = lean_uint64_div(v_oldR_134_, v_r_135_);
v_product_145_ = lean_uint64_mul_mod(v___x_144_, v_s_137_, v_modulus_133_);
v___x_146_ = lean_uint64_dec_le(v_product_145_, v_oldS_136_);
if (v___x_146_ == 0)
{
uint64_t v___x_147_; uint64_t v___x_148_; 
v___x_147_ = lean_uint64_sub(v_product_145_, v_oldS_136_);
v___x_148_ = lean_uint64_sub(v_modulus_133_, v___x_147_);
v___y_139_ = v___x_148_;
goto v___jp_138_;
}
else
{
uint64_t v___x_149_; 
v___x_149_ = lean_uint64_sub(v_oldS_136_, v_product_145_);
v___y_139_ = v___x_149_;
goto v___jp_138_;
}
}
else
{
uint64_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 1ULL;
v___x_151_ = lean_uint64_dec_eq(v_oldR_134_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_box_uint64(v_oldS_136_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
v___jp_138_:
{
uint64_t v___x_140_; 
v___x_140_ = lean_uint64_mod(v_oldR_134_, v_r_135_);
v_oldR_134_ = v_r_135_;
v_r_135_ = v___x_140_;
v_oldS_136_ = v_s_137_;
v_s_137_ = v___y_139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl_go___boxed(lean_object* v_modulus_155_, lean_object* v_oldR_156_, lean_object* v_r_157_, lean_object* v_oldS_158_, lean_object* v_s_159_){
_start:
{
uint64_t v_modulus_boxed_160_; uint64_t v_oldR_boxed_161_; uint64_t v_r_boxed_162_; uint64_t v_oldS_boxed_163_; uint64_t v_s_boxed_164_; lean_object* v_res_165_; 
v_modulus_boxed_160_ = lean_unbox_uint64(v_modulus_155_);
lean_dec_ref(v_modulus_155_);
v_oldR_boxed_161_ = lean_unbox_uint64(v_oldR_156_);
lean_dec_ref(v_oldR_156_);
v_r_boxed_162_ = lean_unbox_uint64(v_r_157_);
lean_dec_ref(v_r_157_);
v_oldS_boxed_163_ = lean_unbox_uint64(v_oldS_158_);
lean_dec_ref(v_oldS_158_);
v_s_boxed_164_ = lean_unbox_uint64(v_s_159_);
lean_dec_ref(v_s_159_);
v_res_165_ = l_UInt64_invModImpl_go(v_modulus_boxed_160_, v_oldR_boxed_161_, v_r_boxed_162_, v_oldS_boxed_163_, v_s_boxed_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl(uint64_t v_a_166_, uint64_t v_modulus_167_){
_start:
{
uint64_t v___x_168_; uint8_t v___x_169_; 
v___x_168_ = 0ULL;
v___x_169_ = lean_uint64_dec_eq(v_modulus_167_, v___x_168_);
if (v___x_169_ == 0)
{
uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_uint64_mod(v_a_166_, v_modulus_167_);
v___x_171_ = 1ULL;
v___x_172_ = lean_uint64_mod(v___x_171_, v_modulus_167_);
v___x_173_ = l_UInt64_invModImpl_go(v_modulus_167_, v___x_170_, v_modulus_167_, v___x_172_, v___x_168_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_invModImpl___boxed(lean_object* v_a_175_, lean_object* v_modulus_176_){
_start:
{
uint64_t v_a_boxed_177_; uint64_t v_modulus_boxed_178_; lean_object* v_res_179_; 
v_a_boxed_177_ = lean_unbox_uint64(v_a_175_);
lean_dec_ref(v_a_175_);
v_modulus_boxed_178_ = lean_unbox_uint64(v_modulus_176_);
lean_dec_ref(v_modulus_176_);
v_res_179_ = l_UInt64_invModImpl(v_a_boxed_177_, v_modulus_boxed_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg(lean_object* v_x_180_, uint64_t v_x_181_, uint64_t v_x_182_, uint64_t v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
lean_object* v_zero_186_; uint8_t v_isZero_187_; 
v_zero_186_ = lean_unsigned_to_nat(0u);
v_isZero_187_ = lean_nat_dec_eq(v_x_180_, v_zero_186_);
if (v_isZero_187_ == 1)
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_h__2_185_);
v___x_188_ = lean_box_uint64(v_x_181_);
v___x_189_ = lean_box_uint64(v_x_182_);
v___x_190_ = lean_box_uint64(v_x_183_);
v___x_191_ = lean_apply_3(v_h__1_184_, v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
else
{
lean_object* v_one_192_; lean_object* v_n_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec(v_h__1_184_);
v_one_192_ = lean_unsigned_to_nat(1u);
v_n_193_ = lean_nat_sub(v_x_180_, v_one_192_);
v___x_194_ = lean_box_uint64(v_x_181_);
v___x_195_ = lean_box_uint64(v_x_182_);
v___x_196_ = lean_box_uint64(v_x_183_);
v___x_197_ = lean_apply_4(v_h__2_185_, v_n_193_, v___x_194_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg___boxed(lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
uint64_t v_x_28__boxed_204_; uint64_t v_x_29__boxed_205_; uint64_t v_x_30__boxed_206_; lean_object* v_res_207_; 
v_x_28__boxed_204_ = lean_unbox_uint64(v_x_199_);
lean_dec_ref(v_x_199_);
v_x_29__boxed_205_ = lean_unbox_uint64(v_x_200_);
lean_dec_ref(v_x_200_);
v_x_30__boxed_206_ = lean_unbox_uint64(v_x_201_);
lean_dec_ref(v_x_201_);
v_res_207_ = l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___redArg(v_x_198_, v_x_28__boxed_204_, v_x_29__boxed_205_, v_x_30__boxed_206_, v_h__1_202_, v_h__2_203_);
lean_dec(v_x_198_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter(lean_object* v_motive_208_, lean_object* v_x_209_, uint64_t v_x_210_, uint64_t v_x_211_, uint64_t v_x_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
lean_object* v_zero_215_; uint8_t v_isZero_216_; 
v_zero_215_ = lean_unsigned_to_nat(0u);
v_isZero_216_ = lean_nat_dec_eq(v_x_209_, v_zero_215_);
if (v_isZero_216_ == 1)
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_h__2_214_);
v___x_217_ = lean_box_uint64(v_x_210_);
v___x_218_ = lean_box_uint64(v_x_211_);
v___x_219_ = lean_box_uint64(v_x_212_);
v___x_220_ = lean_apply_3(v_h__1_213_, v___x_217_, v___x_218_, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v_one_221_; lean_object* v_n_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_213_);
v_one_221_ = lean_unsigned_to_nat(1u);
v_n_222_ = lean_nat_sub(v_x_209_, v_one_221_);
v___x_223_ = lean_box_uint64(v_x_210_);
v___x_224_ = lean_box_uint64(v_x_211_);
v___x_225_ = lean_box_uint64(v_x_212_);
v___x_226_ = lean_apply_4(v_h__2_214_, v_n_222_, v___x_223_, v___x_224_, v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter___boxed(lean_object* v_motive_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_h__1_232_, lean_object* v_h__2_233_){
_start:
{
uint64_t v_x_58__boxed_234_; uint64_t v_x_59__boxed_235_; uint64_t v_x_60__boxed_236_; lean_object* v_res_237_; 
v_x_58__boxed_234_ = lean_unbox_uint64(v_x_229_);
lean_dec_ref(v_x_229_);
v_x_59__boxed_235_ = lean_unbox_uint64(v_x_230_);
lean_dec_ref(v_x_230_);
v_x_60__boxed_236_ = lean_unbox_uint64(v_x_231_);
lean_dec_ref(v_x_231_);
v_res_237_ = l___private_Init_Data_UInt_Modular_0__UInt64_powModChunk_match__1_splitter(v_motive_227_, v_x_228_, v_x_58__boxed_234_, v_x_59__boxed_235_, v_x_60__boxed_236_, v_h__1_232_, v_h__2_233_);
lean_dec(v_x_228_);
return v_res_237_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Modular(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_Modular(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_Modular(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Modular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_Modular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_Modular(builtin);
}
#ifdef __cplusplus
}
#endif
