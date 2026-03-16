// Lean compiler output
// Module: Init.Data.BitVec.Decidable
// Imports: import Init.Ext public import Init.Data.BitVec.Basic public import Init.PropLemmas import Init.Classical import Init.Data.BitVec.Bootstrap
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_BitVec_cons(lean_object*, uint8_t, lean_object*);
uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecZero(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecZero___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecZero(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecSucc___redArg(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecSucc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BitVec_instDecidableForallBitVec___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_instDecidableForallBitVec___redArg___closed__0;
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecZero___redArg(uint8_t v_x_1_){
_start:
{
return v_x_1_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___redArg___boxed(lean_object* v_x_2_){
_start:
{
uint8_t v_x_18__boxed_3_; uint8_t v_res_4_; lean_object* v_r_5_; 
v_x_18__boxed_3_ = lean_unbox(v_x_2_);
v_res_4_ = l_BitVec_instDecidableForallBitVecZero___redArg(v_x_18__boxed_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecZero(lean_object* v_P_6_, uint8_t v_x_7_){
_start:
{
return v_x_7_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecZero___boxed(lean_object* v_P_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_x_21__boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_x_21__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_BitVec_instDecidableForallBitVecZero(v_P_8_, v_x_21__boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecSucc___redArg(uint8_t v_inst_13_){
_start:
{
return v_inst_13_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___redArg___boxed(lean_object* v_inst_14_){
_start:
{
uint8_t v_inst_10__boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_inst_10__boxed_15_ = lean_unbox(v_inst_14_);
v_res_16_ = l_BitVec_instDecidableForallBitVecSucc___redArg(v_inst_10__boxed_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVecSucc(lean_object* v_n_18_, lean_object* v_P_19_, lean_object* v_inst_20_, uint8_t v_inst_21_){
_start:
{
return v_inst_21_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVecSucc___boxed(lean_object* v_n_22_, lean_object* v_P_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
uint8_t v_inst_14__boxed_26_; uint8_t v_res_27_; lean_object* v_r_28_; 
v_inst_14__boxed_26_ = lean_unbox(v_inst_25_);
v_res_27_ = l_BitVec_instDecidableForallBitVecSucc(v_n_22_, v_P_23_, v_inst_24_, v_inst_14__boxed_26_);
lean_dec_ref(v_inst_24_);
lean_dec(v_n_22_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecZero___redArg(uint8_t v_inst_29_){
_start:
{
return v_inst_29_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___redArg___boxed(lean_object* v_inst_30_){
_start:
{
uint8_t v_inst_27__boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v_inst_27__boxed_31_ = lean_unbox(v_inst_30_);
v_res_32_ = l_BitVec_instDecidableExistsBitVecZero___redArg(v_inst_27__boxed_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecZero(lean_object* v_P_34_, uint8_t v_inst_35_){
_start:
{
return v_inst_35_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecZero___boxed(lean_object* v_P_36_, lean_object* v_inst_37_){
_start:
{
uint8_t v_inst_30__boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_inst_30__boxed_38_ = lean_unbox(v_inst_37_);
v_res_39_ = l_BitVec_instDecidableExistsBitVecZero(v_P_36_, v_inst_30__boxed_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecSucc___redArg(uint8_t v_inst_41_){
_start:
{
if (v_inst_41_ == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 1;
return v___x_42_;
}
else
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___redArg___boxed(lean_object* v_inst_44_){
_start:
{
uint8_t v_inst_21__boxed_45_; uint8_t v_res_46_; lean_object* v_r_47_; 
v_inst_21__boxed_45_ = lean_unbox(v_inst_44_);
v_res_46_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_21__boxed_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVecSucc(lean_object* v_n_48_, lean_object* v_P_49_, lean_object* v_inst_50_, uint8_t v_inst_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVecSucc___boxed(lean_object* v_n_53_, lean_object* v_P_54_, lean_object* v_inst_55_, lean_object* v_inst_56_){
_start:
{
uint8_t v_inst_29__boxed_57_; uint8_t v_res_58_; lean_object* v_r_59_; 
v_inst_29__boxed_57_ = lean_unbox(v_inst_56_);
v_res_58_ = l_BitVec_instDecidableExistsBitVecSucc(v_n_53_, v_P_54_, v_inst_55_, v_inst_29__boxed_57_);
lean_dec_ref(v_inst_55_);
lean_dec(v_n_53_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__0(lean_object* v_n_60_, uint8_t v_a_61_, lean_object* v_x_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l_BitVec_cons(v_n_60_, v_a_61_, v_a_63_);
v___x_65_ = lean_apply_1(v_x_62_, v___x_64_);
v___x_66_ = lean_unbox(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed(lean_object* v_n_67_, lean_object* v_a_68_, lean_object* v_x_69_, lean_object* v_a_70_){
_start:
{
uint8_t v_a_boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_a_boxed_71_ = lean_unbox(v_a_68_);
v_res_72_ = l_BitVec_instDecidableForallBitVec___redArg___lam__0(v_n_67_, v_a_boxed_71_, v_x_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec(v_n_67_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
static lean_object* _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0(void){
_start:
{
lean_object* v_zero_74_; lean_object* v___x_75_; 
v_zero_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = l_BitVec_ofNat(v_zero_74_, v_zero_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed(lean_object* v_n_76_, lean_object* v_x_77_, lean_object* v_a_78_){
_start:
{
uint8_t v_a_boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_a_boxed_79_ = lean_unbox(v_a_78_);
v_res_80_ = l_BitVec_instDecidableForallBitVec___redArg___lam__1(v_n_76_, v_x_77_, v_a_boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_zero_84_; uint8_t v_isZero_85_; 
v_zero_84_ = lean_unsigned_to_nat(0u);
v_isZero_85_ = lean_nat_dec_eq(v_x_82_, v_zero_84_);
if (v_isZero_85_ == 1)
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_obj_once(&l_BitVec_instDecidableForallBitVec___redArg___closed__0, &l_BitVec_instDecidableForallBitVec___redArg___closed__0_once, _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0);
v___x_87_ = lean_apply_1(v_x_83_, v___x_86_);
v___x_88_ = lean_unbox(v___x_87_);
return v___x_88_;
}
else
{
lean_object* v_one_89_; lean_object* v_n_90_; lean_object* v___f_91_; uint8_t v___x_92_; 
v_one_89_ = lean_unsigned_to_nat(1u);
v_n_90_ = lean_nat_sub(v_x_82_, v_one_89_);
v___f_91_ = lean_alloc_closure((void*)(l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_91_, 0, v_n_90_);
lean_closure_set(v___f_91_, 1, v_x_83_);
v___x_92_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec___redArg___lam__1(lean_object* v_n_93_, lean_object* v_x_94_, uint8_t v_a_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; uint8_t v___x_98_; 
v___x_96_ = lean_box(v_a_95_);
lean_inc(v_n_93_);
v___f_97_ = lean_alloc_closure((void*)(l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_97_, 0, v_n_93_);
lean_closure_set(v___f_97_, 1, v___x_96_);
lean_closure_set(v___f_97_, 2, v_x_94_);
v___x_98_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_93_, v___f_97_);
lean_dec(v_n_93_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_99_, v_x_100_);
lean_dec(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableForallBitVec(lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_103_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableForallBitVec___boxed(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_BitVec_instDecidableForallBitVec(v_x_107_, v_x_108_, v_x_109_);
lean_dec(v_x_107_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__0(lean_object* v_n_112_, uint8_t v_a_113_, lean_object* v_x_114_, uint8_t v_isZero_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = l_BitVec_cons(v_n_112_, v_a_113_, v_a_116_);
v___x_118_ = lean_apply_1(v_x_114_, v___x_117_);
v___x_119_ = lean_unbox(v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 1;
return v___x_120_;
}
else
{
return v_isZero_115_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed(lean_object* v_n_121_, lean_object* v_a_122_, lean_object* v_x_123_, lean_object* v_isZero_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_a_boxed_126_; uint8_t v_isZero_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_a_boxed_126_ = lean_unbox(v_a_122_);
v_isZero_boxed_127_ = lean_unbox(v_isZero_124_);
v_res_128_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__0(v_n_121_, v_a_boxed_126_, v_x_123_, v_isZero_boxed_127_, v_a_125_);
lean_dec(v_a_125_);
lean_dec(v_n_121_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg___lam__1(lean_object* v_n_130_, lean_object* v_x_131_, uint8_t v_isZero_132_, uint8_t v_a_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___f_136_; uint8_t v___x_137_; 
v___x_134_ = lean_box(v_a_133_);
v___x_135_ = lean_box(v_isZero_132_);
lean_inc(v_n_130_);
v___f_136_ = lean_alloc_closure((void*)(l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_136_, 0, v_n_130_);
lean_closure_set(v___f_136_, 1, v___x_134_);
lean_closure_set(v___f_136_, 2, v_x_131_);
lean_closure_set(v___f_136_, 3, v___x_135_);
v___x_137_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_130_, v___f_136_);
lean_dec(v_n_130_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed(lean_object* v_n_138_, lean_object* v_x_139_, lean_object* v_isZero_140_, lean_object* v_a_141_){
_start:
{
uint8_t v_isZero_boxed_142_; uint8_t v_a_boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v_isZero_boxed_142_ = lean_unbox(v_isZero_140_);
v_a_boxed_143_ = lean_unbox(v_a_141_);
v_res_144_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__1(v_n_138_, v_x_139_, v_isZero_boxed_142_, v_a_boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec___redArg(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_zero_148_; uint8_t v_isZero_149_; 
v_zero_148_ = lean_unsigned_to_nat(0u);
v_isZero_149_ = lean_nat_dec_eq(v_x_146_, v_zero_148_);
if (v_isZero_149_ == 1)
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_obj_once(&l_BitVec_instDecidableForallBitVec___redArg___closed__0, &l_BitVec_instDecidableForallBitVec___redArg___closed__0_once, _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0);
v___x_151_ = lean_apply_1(v_x_147_, v___x_150_);
v___x_152_ = lean_unbox(v___x_151_);
return v___x_152_;
}
else
{
lean_object* v_one_153_; lean_object* v_n_154_; lean_object* v___x_155_; lean_object* v___f_156_; uint8_t v___x_157_; uint8_t v___x_158_; 
v_one_153_ = lean_unsigned_to_nat(1u);
v_n_154_ = lean_nat_sub(v_x_146_, v_one_153_);
v___x_155_ = lean_box(v_isZero_149_);
v___f_156_ = lean_alloc_closure((void*)(l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_156_, 0, v_n_154_);
lean_closure_set(v___f_156_, 1, v_x_147_);
lean_closure_set(v___f_156_, 2, v___x_155_);
v___x_157_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_156_);
v___x_158_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___redArg___boxed(lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_159_, v_x_160_);
lean_dec(v_x_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instDecidableExistsBitVec(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_163_, v_x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDecidableExistsBitVec___boxed(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_BitVec_instDecidableExistsBitVec(v_x_167_, v_x_168_, v_x_169_);
lean_dec(v_x_167_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Decidable(builtin);
}
#ifdef __cplusplus
}
#endif
