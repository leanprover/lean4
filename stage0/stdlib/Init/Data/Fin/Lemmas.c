// Lean compiler output
// Module: Init.Data.Fin.Lemmas
// Imports: public import Init.Ext public import Init.Data.Nat.Div.Basic public import Init.Data.Order.Classes public import Init.NotationExtra import Init.ByCases import Init.Data.Nat.Lemmas import Init.Data.Nat.Linear import Init.Omega import Init.TacticsExtra import Init.Hints
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast(lean_object*, lean_object*);
static lean_once_cell_t l_Fin_intCast___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_intCast___redArg___closed__0;
LEAN_EXPORT lean_object* l_Fin_intCast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_intCast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_intCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_intCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_IntCast_instIntCast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_IntCast_instIntCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRecOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRecOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succRecOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_inductionOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_inductionOn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_inductionOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_reverseInduction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lastCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addCases___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addCases___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0(lean_object* v_n_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_nat_mod(v_a_2_, v_n_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast___redArg___lam__0___boxed(lean_object* v_n_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Fin_NatCast_instNatCast___redArg___lam__0(v_n_4_, v_a_5_);
lean_dec(v_a_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast___redArg(lean_object* v_n_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(l_Fin_NatCast_instNatCast___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_8_, 0, v_n_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* l_Fin_NatCast_instNatCast(lean_object* v_n_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = lean_alloc_closure((void*)(l_Fin_NatCast_instNatCast___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_11_, 0, v_n_9_);
return v___f_11_;
}
}
static lean_object* _init_l_Fin_intCast___redArg___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_nat_to_int(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Fin_intCast___redArg(lean_object* v_n_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_obj_once(&l_Fin_intCast___redArg___closed__0, &l_Fin_intCast___redArg___closed__0_once, _init_l_Fin_intCast___redArg___closed__0);
v___x_17_ = lean_int_dec_le(v___x_16_, v_a_15_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_nat_abs(v_a_15_);
v___x_19_ = lean_nat_mod(v___x_18_, v_n_14_);
lean_dec(v___x_18_);
v___x_20_ = lean_nat_sub(v_n_14_, v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = lean_nat_mod(v___x_20_, v_n_14_);
lean_dec(v___x_20_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_nat_abs(v_a_15_);
v___x_23_ = lean_nat_mod(v___x_22_, v_n_14_);
lean_dec(v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_intCast___redArg___boxed(lean_object* v_n_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Fin_intCast___redArg(v_n_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec(v_n_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Fin_intCast(lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Fin_intCast___redArg(v_n_27_, v_a_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Fin_intCast___boxed(lean_object* v_n_31_, lean_object* v_inst_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Fin_intCast(v_n_31_, v_inst_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec(v_n_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Fin_IntCast_instIntCast___redArg(lean_object* v_n_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_alloc_closure((void*)(l_Fin_intCast___boxed), 3, 2);
lean_closure_set(v___x_36_, 0, v_n_35_);
lean_closure_set(v___x_36_, 1, lean_box(0));
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Fin_IntCast_instIntCast(lean_object* v_n_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_closure((void*)(l_Fin_intCast___boxed), 3, 2);
lean_closure_set(v___x_39_, 0, v_n_37_);
lean_closure_set(v___x_39_, 1, lean_box(0));
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRec___redArg(lean_object* v_zero_40_, lean_object* v_succ_41_, lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
lean_object* v_zero_44_; uint8_t v_isZero_45_; lean_object* v_one_46_; lean_object* v_n_47_; uint8_t v_isZero_48_; 
v_zero_44_ = lean_unsigned_to_nat(0u);
v_isZero_45_ = lean_nat_dec_eq(v_x_42_, v_zero_44_);
v_one_46_ = lean_unsigned_to_nat(1u);
v_n_47_ = lean_nat_sub(v_x_42_, v_one_46_);
v_isZero_48_ = lean_nat_dec_eq(v_x_43_, v_zero_44_);
if (v_isZero_48_ == 1)
{
lean_object* v___x_49_; 
lean_dec(v_succ_41_);
v___x_49_ = lean_apply_1(v_zero_40_, v_n_47_);
return v___x_49_;
}
else
{
lean_object* v_n_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_n_50_ = lean_nat_sub(v_x_43_, v_one_46_);
lean_inc(v_succ_41_);
v___x_51_ = l_Fin_succRec___redArg(v_zero_40_, v_succ_41_, v_n_47_, v_n_50_);
v___x_52_ = lean_apply_3(v_succ_41_, v_n_47_, v_n_50_, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_succRec___redArg___boxed(lean_object* v_zero_53_, lean_object* v_succ_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Fin_succRec___redArg(v_zero_53_, v_succ_54_, v_x_55_, v_x_56_);
lean_dec(v_x_56_);
lean_dec(v_x_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRec(lean_object* v_motive_58_, lean_object* v_zero_59_, lean_object* v_succ_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Fin_succRec___redArg(v_zero_59_, v_succ_60_, v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRec___boxed(lean_object* v_motive_64_, lean_object* v_zero_65_, lean_object* v_succ_66_, lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Fin_succRec(v_motive_64_, v_zero_65_, v_succ_66_, v_x_67_, v_x_68_);
lean_dec(v_x_68_);
lean_dec(v_x_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRecOn___redArg(lean_object* v_n_70_, lean_object* v_i_71_, lean_object* v_zero_72_, lean_object* v_succ_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Fin_succRec___redArg(v_zero_72_, v_succ_73_, v_n_70_, v_i_71_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRecOn___redArg___boxed(lean_object* v_n_75_, lean_object* v_i_76_, lean_object* v_zero_77_, lean_object* v_succ_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Fin_succRecOn___redArg(v_n_75_, v_i_76_, v_zero_77_, v_succ_78_);
lean_dec(v_i_76_);
lean_dec(v_n_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRecOn(lean_object* v_n_80_, lean_object* v_i_81_, lean_object* v_motive_82_, lean_object* v_zero_83_, lean_object* v_succ_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Fin_succRec___redArg(v_zero_83_, v_succ_84_, v_n_80_, v_i_81_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Fin_succRecOn___boxed(lean_object* v_n_86_, lean_object* v_i_87_, lean_object* v_motive_88_, lean_object* v_zero_89_, lean_object* v_succ_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Fin_succRecOn(v_n_86_, v_i_87_, v_motive_88_, v_zero_89_, v_succ_90_);
lean_dec(v_i_87_);
lean_dec(v_n_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction_go___redArg(lean_object* v_zero_92_, lean_object* v_succ_93_, lean_object* v_i_94_){
_start:
{
lean_object* v_zero_95_; uint8_t v_isZero_96_; 
v_zero_95_ = lean_unsigned_to_nat(0u);
v_isZero_96_ = lean_nat_dec_eq(v_i_94_, v_zero_95_);
if (v_isZero_96_ == 1)
{
lean_dec(v_succ_93_);
lean_inc(v_zero_92_);
return v_zero_92_;
}
else
{
lean_object* v_one_97_; lean_object* v_n_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_one_97_ = lean_unsigned_to_nat(1u);
v_n_98_ = lean_nat_sub(v_i_94_, v_one_97_);
lean_inc(v_succ_93_);
v___x_99_ = l_Fin_induction_go___redArg(v_zero_92_, v_succ_93_, v_n_98_);
v___x_100_ = lean_apply_2(v_succ_93_, v_n_98_, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_induction_go___redArg___boxed(lean_object* v_zero_101_, lean_object* v_succ_102_, lean_object* v_i_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Fin_induction_go___redArg(v_zero_101_, v_succ_102_, v_i_103_);
lean_dec(v_i_103_);
lean_dec(v_zero_101_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction_go(lean_object* v_n_105_, lean_object* v_motive_106_, lean_object* v_zero_107_, lean_object* v_succ_108_, lean_object* v_i_109_, lean_object* v_hi_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Fin_induction_go___redArg(v_zero_107_, v_succ_108_, v_i_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction_go___boxed(lean_object* v_n_112_, lean_object* v_motive_113_, lean_object* v_zero_114_, lean_object* v_succ_115_, lean_object* v_i_116_, lean_object* v_hi_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Fin_induction_go(v_n_112_, v_motive_113_, v_zero_114_, v_succ_115_, v_i_116_, v_hi_117_);
lean_dec(v_i_116_);
lean_dec(v_zero_114_);
lean_dec(v_n_112_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction___redArg(lean_object* v_zero_119_, lean_object* v_succ_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Fin_induction_go___redArg(v_zero_119_, v_succ_120_, v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction___redArg___boxed(lean_object* v_zero_123_, lean_object* v_succ_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Fin_induction___redArg(v_zero_123_, v_succ_124_, v_x_125_);
lean_dec(v_x_125_);
lean_dec(v_zero_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction(lean_object* v_n_127_, lean_object* v_motive_128_, lean_object* v_zero_129_, lean_object* v_succ_130_, lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Fin_induction_go___redArg(v_zero_129_, v_succ_130_, v_x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Fin_induction___boxed(lean_object* v_n_133_, lean_object* v_motive_134_, lean_object* v_zero_135_, lean_object* v_succ_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Fin_induction(v_n_133_, v_motive_134_, v_zero_135_, v_succ_136_, v_x_137_);
lean_dec(v_x_137_);
lean_dec(v_zero_135_);
lean_dec(v_n_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Fin_inductionOn___redArg(lean_object* v_i_139_, lean_object* v_zero_140_, lean_object* v_succ_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Fin_induction_go___redArg(v_zero_140_, v_succ_141_, v_i_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Fin_inductionOn___redArg___boxed(lean_object* v_i_143_, lean_object* v_zero_144_, lean_object* v_succ_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Fin_inductionOn___redArg(v_i_143_, v_zero_144_, v_succ_145_);
lean_dec(v_zero_144_);
lean_dec(v_i_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Fin_inductionOn(lean_object* v_n_147_, lean_object* v_i_148_, lean_object* v_motive_149_, lean_object* v_zero_150_, lean_object* v_succ_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Fin_induction_go___redArg(v_zero_150_, v_succ_151_, v_i_148_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Fin_inductionOn___boxed(lean_object* v_n_153_, lean_object* v_i_154_, lean_object* v_motive_155_, lean_object* v_zero_156_, lean_object* v_succ_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Fin_inductionOn(v_n_153_, v_i_154_, v_motive_155_, v_zero_156_, v_succ_157_);
lean_dec(v_zero_156_);
lean_dec(v_i_154_);
lean_dec(v_n_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___redArg___lam__0(lean_object* v_succ_159_, lean_object* v_i_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_1(v_succ_159_, v_i_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___redArg___lam__0___boxed(lean_object* v_succ_163_, lean_object* v_i_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Fin_cases___redArg___lam__0(v_succ_163_, v_i_164_, v_x_165_);
lean_dec(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___redArg(lean_object* v_zero_167_, lean_object* v_succ_168_, lean_object* v_i_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___x_171_; 
v___f_170_ = lean_alloc_closure((void*)(l_Fin_cases___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_170_, 0, v_succ_168_);
v___x_171_ = l_Fin_induction_go___redArg(v_zero_167_, v___f_170_, v_i_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___redArg___boxed(lean_object* v_zero_172_, lean_object* v_succ_173_, lean_object* v_i_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Fin_cases___redArg(v_zero_172_, v_succ_173_, v_i_174_);
lean_dec(v_i_174_);
lean_dec(v_zero_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Fin_cases(lean_object* v_n_176_, lean_object* v_motive_177_, lean_object* v_zero_178_, lean_object* v_succ_179_, lean_object* v_i_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Fin_cases___redArg(v_zero_178_, v_succ_179_, v_i_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Fin_cases___boxed(lean_object* v_n_182_, lean_object* v_motive_183_, lean_object* v_zero_184_, lean_object* v_succ_185_, lean_object* v_i_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Fin_cases(v_n_182_, v_motive_183_, v_zero_184_, v_succ_185_, v_i_186_);
lean_dec(v_i_186_);
lean_dec(v_zero_184_);
lean_dec(v_n_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go___redArg(lean_object* v_cast_188_, lean_object* v_i_189_, lean_object* v_j_190_, lean_object* v_x_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_eq(v_i_189_, v_j_190_);
if (v___x_192_ == 0)
{
lean_object* v_zero_193_; uint8_t v_isZero_194_; lean_object* v_one_195_; lean_object* v_n_196_; lean_object* v___x_197_; 
v_zero_193_ = lean_unsigned_to_nat(0u);
v_isZero_194_ = lean_nat_dec_eq(v_j_190_, v_zero_193_);
v_one_195_ = lean_unsigned_to_nat(1u);
v_n_196_ = lean_nat_sub(v_j_190_, v_one_195_);
lean_dec(v_j_190_);
lean_inc(v_cast_188_);
lean_inc(v_n_196_);
v___x_197_ = lean_apply_2(v_cast_188_, v_n_196_, v_x_191_);
v_j_190_ = v_n_196_;
v_x_191_ = v___x_197_;
goto _start;
}
else
{
lean_dec(v_j_190_);
lean_dec(v_cast_188_);
return v_x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go___redArg___boxed(lean_object* v_cast_199_, lean_object* v_i_200_, lean_object* v_j_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Fin_reverseInduction_go___redArg(v_cast_199_, v_i_200_, v_j_201_, v_x_202_);
lean_dec(v_i_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go(lean_object* v_n_204_, lean_object* v_motive_205_, lean_object* v_cast_206_, lean_object* v_i_207_, lean_object* v_j_208_, lean_object* v_h_209_, lean_object* v_h2_210_, lean_object* v_x_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Fin_reverseInduction_go___redArg(v_cast_206_, v_i_207_, v_j_208_, v_x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction_go___boxed(lean_object* v_n_213_, lean_object* v_motive_214_, lean_object* v_cast_215_, lean_object* v_i_216_, lean_object* v_j_217_, lean_object* v_h_218_, lean_object* v_h2_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Fin_reverseInduction_go(v_n_213_, v_motive_214_, v_cast_215_, v_i_216_, v_j_217_, v_h_218_, v_h2_219_, v_x_220_);
lean_dec(v_i_216_);
lean_dec(v_n_213_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction___redArg(lean_object* v_n_222_, lean_object* v_last_223_, lean_object* v_cast_224_, lean_object* v_i_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Fin_reverseInduction_go___redArg(v_cast_224_, v_i_225_, v_n_222_, v_last_223_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction___redArg___boxed(lean_object* v_n_227_, lean_object* v_last_228_, lean_object* v_cast_229_, lean_object* v_i_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Fin_reverseInduction___redArg(v_n_227_, v_last_228_, v_cast_229_, v_i_230_);
lean_dec(v_i_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction(lean_object* v_n_232_, lean_object* v_motive_233_, lean_object* v_last_234_, lean_object* v_cast_235_, lean_object* v_i_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Fin_reverseInduction_go___redArg(v_cast_235_, v_i_236_, v_n_232_, v_last_234_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Fin_reverseInduction___boxed(lean_object* v_n_238_, lean_object* v_motive_239_, lean_object* v_last_240_, lean_object* v_cast_241_, lean_object* v_i_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Fin_reverseInduction(v_n_238_, v_motive_239_, v_last_240_, v_cast_241_, v_i_242_);
lean_dec(v_i_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg(lean_object* v_j_244_, lean_object* v_x_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_){
_start:
{
lean_object* v_zero_248_; uint8_t v_isZero_249_; 
v_zero_248_ = lean_unsigned_to_nat(0u);
v_isZero_249_ = lean_nat_dec_eq(v_j_244_, v_zero_248_);
if (v_isZero_249_ == 1)
{
lean_object* v___x_250_; 
lean_dec(v_h__2_247_);
v___x_250_ = lean_apply_4(v_h__1_246_, lean_box(0), lean_box(0), v_x_245_, lean_box(0));
return v___x_250_;
}
else
{
lean_object* v_one_251_; lean_object* v_n_252_; lean_object* v___x_253_; 
lean_dec(v_h__1_246_);
v_one_251_ = lean_unsigned_to_nat(1u);
v_n_252_ = lean_nat_sub(v_j_244_, v_one_251_);
v___x_253_ = lean_apply_5(v_h__2_247_, v_n_252_, lean_box(0), lean_box(0), v_x_245_, lean_box(0));
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg___boxed(lean_object* v_j_254_, lean_object* v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg(v_j_254_, v_x_255_, v_h__1_256_, v_h__2_257_);
lean_dec(v_j_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter(lean_object* v_n_259_, lean_object* v_motive_260_, lean_object* v_i_261_, lean_object* v_motive_262_, lean_object* v_j_263_, lean_object* v_h_264_, lean_object* v_h2_265_, lean_object* v_x_266_, lean_object* v_hi_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
lean_object* v_zero_270_; uint8_t v_isZero_271_; 
v_zero_270_ = lean_unsigned_to_nat(0u);
v_isZero_271_ = lean_nat_dec_eq(v_j_263_, v_zero_270_);
if (v_isZero_271_ == 1)
{
lean_object* v___x_272_; 
lean_dec(v_h__2_269_);
v___x_272_ = lean_apply_4(v_h__1_268_, lean_box(0), lean_box(0), v_x_266_, lean_box(0));
return v___x_272_;
}
else
{
lean_object* v_one_273_; lean_object* v_n_274_; lean_object* v___x_275_; 
lean_dec(v_h__1_268_);
v_one_273_ = lean_unsigned_to_nat(1u);
v_n_274_ = lean_nat_sub(v_j_263_, v_one_273_);
v___x_275_ = lean_apply_5(v_h__2_269_, v_n_274_, lean_box(0), lean_box(0), v_x_266_, lean_box(0));
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___boxed(lean_object* v_n_276_, lean_object* v_motive_277_, lean_object* v_i_278_, lean_object* v_motive_279_, lean_object* v_j_280_, lean_object* v_h_281_, lean_object* v_h2_282_, lean_object* v_x_283_, lean_object* v_hi_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter(v_n_276_, v_motive_277_, v_i_278_, v_motive_279_, v_j_280_, v_h_281_, v_h2_282_, v_x_283_, v_hi_284_, v_h__1_285_, v_h__2_286_);
lean_dec(v_j_280_);
lean_dec(v_i_278_);
lean_dec(v_n_276_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg___lam__0(lean_object* v_cast_288_, lean_object* v_i_289_, lean_object* v_x_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_apply_1(v_cast_288_, v_i_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg___lam__0___boxed(lean_object* v_cast_292_, lean_object* v_i_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Fin_lastCases___redArg___lam__0(v_cast_292_, v_i_293_, v_x_294_);
lean_dec(v_x_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg(lean_object* v_n_296_, lean_object* v_last_297_, lean_object* v_cast_298_, lean_object* v_i_299_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; 
v___f_300_ = lean_alloc_closure((void*)(l_Fin_lastCases___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_300_, 0, v_cast_298_);
v___x_301_ = l_Fin_reverseInduction_go___redArg(v___f_300_, v_i_299_, v_n_296_, v_last_297_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases___redArg___boxed(lean_object* v_n_302_, lean_object* v_last_303_, lean_object* v_cast_304_, lean_object* v_i_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Fin_lastCases___redArg(v_n_302_, v_last_303_, v_cast_304_, v_i_305_);
lean_dec(v_i_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases(lean_object* v_n_307_, lean_object* v_motive_308_, lean_object* v_last_309_, lean_object* v_cast_310_, lean_object* v_i_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Fin_lastCases___redArg(v_n_307_, v_last_309_, v_cast_310_, v_i_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Fin_lastCases___boxed(lean_object* v_n_313_, lean_object* v_motive_314_, lean_object* v_last_315_, lean_object* v_cast_316_, lean_object* v_i_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Fin_lastCases(v_n_313_, v_motive_314_, v_last_315_, v_cast_316_, v_i_317_);
lean_dec(v_i_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Fin_addCases___redArg(lean_object* v_m_319_, lean_object* v_left_320_, lean_object* v_right_321_, lean_object* v_i_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_lt(v_i_322_, v_m_319_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_left_320_);
v___x_324_ = lean_nat_sub(v_i_322_, v_m_319_);
lean_dec(v_i_322_);
v___x_325_ = lean_apply_1(v_right_321_, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
lean_dec(v_right_321_);
v___x_326_ = lean_apply_1(v_left_320_, v_i_322_);
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_addCases___redArg___boxed(lean_object* v_m_327_, lean_object* v_left_328_, lean_object* v_right_329_, lean_object* v_i_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Fin_addCases___redArg(v_m_327_, v_left_328_, v_right_329_, v_i_330_);
lean_dec(v_m_327_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Fin_addCases(lean_object* v_m_332_, lean_object* v_n_333_, lean_object* v_motive_334_, lean_object* v_left_335_, lean_object* v_right_336_, lean_object* v_i_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Fin_addCases___redArg(v_m_332_, v_left_335_, v_right_336_, v_i_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Fin_addCases___boxed(lean_object* v_m_339_, lean_object* v_n_340_, lean_object* v_motive_341_, lean_object* v_left_342_, lean_object* v_right_343_, lean_object* v_i_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Fin_addCases(v_m_339_, v_n_340_, v_motive_341_, v_left_342_, v_right_343_, v_i_344_);
lean_dec(v_n_340_);
lean_dec(v_m_339_);
return v_res_345_;
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Hints(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Hints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_Hints(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Hints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
