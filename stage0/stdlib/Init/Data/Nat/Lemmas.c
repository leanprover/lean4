// Lean compiler output
// Module: Init.Data.Nat.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.Data.Nat.Log2 import all Init.Data.Nat.Log2 import Init.TacticsExtra public import Init.Data.Nat.Div.Basic public import Init.PropLemmas import Init.ByCases import Init.Data.Nat.Dvd import Init.Data.Nat.Linear import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Omega import Init.RCases
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLT___redArg___lam__0(lean_object* v_x_1_, lean_object* v_n_2_, lean_object* v_h_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_2(v_x_1_, v_n_2_, lean_box(0));
v___x_5_ = lean_unbox(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLT___redArg___lam__0___boxed(lean_object* v_x_6_, lean_object* v_n_7_, lean_object* v_h_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Nat_decidableBallLT___redArg___lam__0(v_x_6_, v_n_7_, v_h_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLT___redArg(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_zero_13_; uint8_t v_isZero_14_; 
v_zero_13_ = lean_unsigned_to_nat(0u);
v_isZero_14_ = lean_nat_dec_eq(v_x_11_, v_zero_13_);
if (v_isZero_14_ == 1)
{
lean_dec_ref(v_x_12_);
return v_isZero_14_;
}
else
{
lean_object* v___f_15_; lean_object* v_one_16_; lean_object* v_n_17_; uint8_t v___x_18_; 
lean_inc_ref(v_x_12_);
v___f_15_ = lean_alloc_closure((void*)(l_Nat_decidableBallLT___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_15_, 0, v_x_12_);
v_one_16_ = lean_unsigned_to_nat(1u);
v_n_17_ = lean_nat_sub(v_x_11_, v_one_16_);
v___x_18_ = l_Nat_decidableBallLT___redArg(v_n_17_, v___f_15_);
if (v___x_18_ == 0)
{
lean_dec(v_n_17_);
lean_dec_ref(v_x_12_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lean_apply_2(v_x_12_, v_n_17_, lean_box(0));
v___x_20_ = lean_unbox(v___x_19_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLT___redArg___boxed(lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Nat_decidableBallLT___redArg(v_x_21_, v_x_22_);
lean_dec(v_x_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLT(lean_object* v_x_25_, lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l_Nat_decidableBallLT___redArg(v_x_25_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLT___boxed(lean_object* v_x_29_, lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Nat_decidableBallLT(v_x_29_, v_x_30_, v_x_31_);
lean_dec(v_x_29_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object* v_inst_34_, lean_object* v_n_35_, lean_object* v_h_36_){
_start:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_apply_1(v_inst_34_, v_n_35_);
v___x_38_ = lean_unbox(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object* v_inst_39_, lean_object* v_n_40_, lean_object* v_h_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_39_, v_n_40_, v_h_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg(lean_object* v_n_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___f_46_; uint8_t v___x_47_; 
v___f_46_ = lean_alloc_closure((void*)(l_Nat_decidableForallFin___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_46_, 0, v_inst_45_);
v___x_47_ = l_Nat_decidableBallLT___redArg(v_n_44_, v___f_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object* v_n_48_, lean_object* v_inst_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Nat_decidableForallFin___redArg(v_n_48_, v_inst_49_);
lean_dec(v_n_48_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin(lean_object* v_n_52_, lean_object* v_P_53_, lean_object* v_inst_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = l_Nat_decidableForallFin___redArg(v_n_52_, v_inst_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object* v_n_56_, lean_object* v_P_57_, lean_object* v_inst_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Nat_decidableForallFin(v_n_56_, v_P_57_, v_inst_58_);
lean_dec(v_n_56_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg___lam__0(lean_object* v_inst_61_, lean_object* v_n_62_, lean_object* v_h_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_apply_2(v_inst_61_, v_n_62_, lean_box(0));
v___x_65_ = lean_unbox(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___lam__0___boxed(lean_object* v_inst_66_, lean_object* v_n_67_, lean_object* v_h_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Nat_decidableBallLE___redArg___lam__0(v_inst_66_, v_n_67_, v_h_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object* v_n_71_, lean_object* v_inst_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___f_73_ = lean_alloc_closure((void*)(l_Nat_decidableBallLE___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_73_, 0, v_inst_72_);
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_n_71_, v___x_74_);
v___x_76_ = l_Nat_decidableBallLT___redArg(v___x_75_, v___f_73_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object* v_n_77_, lean_object* v_inst_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Nat_decidableBallLE___redArg(v_n_77_, v_inst_78_);
lean_dec(v_n_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object* v_n_81_, lean_object* v_P_82_, lean_object* v_inst_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l_Nat_decidableBallLE___redArg(v_n_81_, v_inst_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object* v_n_85_, lean_object* v_P_86_, lean_object* v_inst_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Nat_decidableBallLE(v_n_85_, v_P_86_, v_inst_87_);
lean_dec(v_n_85_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT___redArg(lean_object* v_h_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_zero_92_; uint8_t v_isZero_93_; 
v_zero_92_ = lean_unsigned_to_nat(0u);
v_isZero_93_ = lean_nat_dec_eq(v_x_91_, v_zero_92_);
if (v_isZero_93_ == 1)
{
uint8_t v___x_94_; 
lean_dec_ref(v_h_90_);
v___x_94_ = 0;
return v___x_94_;
}
else
{
lean_object* v_one_95_; lean_object* v_n_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_one_95_ = lean_unsigned_to_nat(1u);
v_n_96_ = lean_nat_sub(v_x_91_, v_one_95_);
lean_inc_ref(v_h_90_);
lean_inc(v_n_96_);
v___x_97_ = lean_apply_1(v_h_90_, v_n_96_);
v___x_98_ = l_Nat_decidableExistsLT___redArg(v_h_90_, v_n_96_);
lean_dec(v_n_96_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
v___x_99_ = lean_unbox(v___x_97_);
return v___x_99_;
}
else
{
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT___redArg___boxed(lean_object* v_h_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Nat_decidableExistsLT___redArg(v_h_100_, v_x_101_);
lean_dec(v_x_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT(lean_object* v_p_104_, lean_object* v_h_105_, lean_object* v_x_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Nat_decidableExistsLT___redArg(v_h_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT___boxed(lean_object* v_p_108_, lean_object* v_h_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Nat_decidableExistsLT(v_p_108_, v_h_109_, v_x_110_);
lean_dec(v_x_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object* v_inst_113_, lean_object* v_n_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_n_114_, v___x_115_);
v___x_117_ = l_Nat_decidableExistsLT___redArg(v_inst_113_, v___x_116_);
lean_dec(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object* v_inst_118_, lean_object* v_n_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Nat_decidableExistsLE___redArg(v_inst_118_, v_n_119_);
lean_dec(v_n_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object* v_p_122_, lean_object* v_inst_123_, lean_object* v_n_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = l_Nat_decidableExistsLE___redArg(v_inst_123_, v_n_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object* v_p_126_, lean_object* v_inst_127_, lean_object* v_n_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Nat_decidableExistsLE(v_p_126_, v_inst_127_, v_n_128_);
lean_dec(v_n_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27___redArg___lam__0(lean_object* v_I_131_, lean_object* v_m_132_, lean_object* v_h_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_apply_2(v_I_131_, v_m_132_, lean_box(0));
v___x_135_ = lean_unbox(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed(lean_object* v_I_136_, lean_object* v_m_137_, lean_object* v_h_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Nat_decidableExistsLT_x27___redArg___lam__0(v_I_136_, v_m_137_, v_h_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27___redArg(lean_object* v_k_141_, lean_object* v_I_142_){
_start:
{
lean_object* v_zero_143_; uint8_t v_isZero_144_; 
v_zero_143_ = lean_unsigned_to_nat(0u);
v_isZero_144_ = lean_nat_dec_eq(v_k_141_, v_zero_143_);
if (v_isZero_144_ == 1)
{
uint8_t v___x_145_; 
lean_dec_ref(v_I_142_);
v___x_145_ = 0;
return v___x_145_;
}
else
{
lean_object* v___f_146_; lean_object* v_one_147_; lean_object* v_n_148_; uint8_t v___x_149_; 
lean_inc_ref(v_I_142_);
v___f_146_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_146_, 0, v_I_142_);
v_one_147_ = lean_unsigned_to_nat(1u);
v_n_148_ = lean_nat_sub(v_k_141_, v_one_147_);
v___x_149_ = l_Nat_decidableExistsLT_x27___redArg(v_n_148_, v___f_146_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_apply_2(v_I_142_, v_n_148_, lean_box(0));
v___x_151_ = lean_unbox(v___x_150_);
return v___x_151_;
}
else
{
lean_dec(v_n_148_);
lean_dec_ref(v_I_142_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27___redArg___boxed(lean_object* v_k_152_, lean_object* v_I_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Nat_decidableExistsLT_x27___redArg(v_k_152_, v_I_153_);
lean_dec(v_k_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27(lean_object* v_k_156_, lean_object* v_p_157_, lean_object* v_I_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Nat_decidableExistsLT_x27___redArg(v_k_156_, v_I_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27___boxed(lean_object* v_k_160_, lean_object* v_p_161_, lean_object* v_I_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Nat_decidableExistsLT_x27(v_k_160_, v_p_161_, v_I_162_);
lean_dec(v_k_160_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object* v_k_165_, lean_object* v_I_166_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___f_167_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_167_, 0, v_I_166_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v_k_165_, v___x_168_);
v___x_170_ = l_Nat_decidableExistsLT_x27___redArg(v___x_169_, v___f_167_);
lean_dec(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object* v_k_171_, lean_object* v_I_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Nat_decidableExistsLE_x27___redArg(v_k_171_, v_I_172_);
lean_dec(v_k_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object* v_k_175_, lean_object* v_p_176_, lean_object* v_I_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = l_Nat_decidableExistsLE_x27___redArg(v_k_175_, v_I_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object* v_k_179_, lean_object* v_p_180_, lean_object* v_I_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Nat_decidableExistsLE_x27(v_k_179_, v_p_180_, v_I_181_);
lean_dec(v_k_179_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object* v_n_184_, lean_object* v_inst_185_, lean_object* v_a_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_lt(v_a_186_, v_n_184_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
lean_dec(v_a_186_);
lean_dec_ref(v_inst_185_);
v___x_188_ = 1;
return v___x_188_;
}
else
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = lean_apply_1(v_inst_185_, v_a_186_);
v___x_190_ = lean_unbox(v___x_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object* v_n_191_, lean_object* v_inst_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_191_, v_inst_192_, v_a_193_);
lean_dec(v_n_191_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object* v_n_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; uint8_t v___x_199_; 
lean_inc(v_n_196_);
v___f_198_ = lean_alloc_closure((void*)(l_Nat_decidableExistsFin___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_198_, 0, v_n_196_);
lean_closure_set(v___f_198_, 1, v_inst_197_);
v___x_199_ = l_Nat_decidableExistsLT___redArg(v___f_198_, v_n_196_);
lean_dec(v_n_196_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object* v_n_200_, lean_object* v_inst_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Nat_decidableExistsFin___redArg(v_n_200_, v_inst_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object* v_n_204_, lean_object* v_P_205_, lean_object* v_inst_206_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = l_Nat_decidableExistsFin___redArg(v_n_204_, v_inst_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object* v_n_208_, lean_object* v_P_209_, lean_object* v_inst_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Nat_decidableExistsFin(v_n_208_, v_P_209_, v_inst_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
