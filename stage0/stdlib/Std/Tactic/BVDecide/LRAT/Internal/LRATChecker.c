// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
// Imports: public import Std.Tactic.BVDecide.LRAT.Actions public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "success"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "out of proof"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rup failure"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(lean_object* v_success_28_){
_start:
{
lean_inc(v_success_28_);
return v_success_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg___boxed(lean_object* v_success_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(v_success_29_);
lean_dec(v_success_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_success_34_){
_start:
{
lean_inc(v_success_34_);
return v_success_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_success_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_success_38_);
lean_dec(v_success_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(lean_object* v_outOfProof_41_){
_start:
{
lean_inc(v_outOfProof_41_);
return v_outOfProof_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg___boxed(lean_object* v_outOfProof_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(v_outOfProof_42_);
lean_dec(v_outOfProof_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_outOfProof_47_){
_start:
{
lean_inc(v_outOfProof_47_);
return v_outOfProof_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_outOfProof_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_outOfProof_51_);
lean_dec(v_outOfProof_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(lean_object* v_rupFailure_54_){
_start:
{
lean_inc(v_rupFailure_54_);
return v_rupFailure_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg___boxed(lean_object* v_rupFailure_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(v_rupFailure_55_);
lean_dec(v_rupFailure_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_rupFailure_60_){
_start:
{
lean_inc(v_rupFailure_60_);
return v_rupFailure_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_rupFailure_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_rupFailure_64_);
lean_dec(v_rupFailure_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat___boxed(lean_object* v_n_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(v_n_77_);
lean_dec(v_n_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_80_);
v___x_83_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(lean_object* v_x_85_, lean_object* v_y_86_){
_start:
{
uint8_t v_x_13__boxed_87_; uint8_t v_y_14__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_13__boxed_87_ = lean_unbox(v_x_85_);
v_y_14__boxed_88_ = lean_unbox(v_y_86_);
v_res_89_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(v_x_13__boxed_87_, v_y_14__boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(uint8_t v_x_94_){
_start:
{
switch(v_x_94_)
{
case 0:
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0));
return v___x_95_;
}
case 1:
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1));
return v___x_96_;
}
default: 
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2));
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_x_36__boxed_99_; lean_object* v_res_100_; 
v_x_36__boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(v_x_36__boxed_99_);
return v_res_100_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_f_105_, lean_object* v_prf_106_){
_start:
{
if (lean_obj_tag(v_prf_106_) == 0)
{
uint8_t v___x_107_; 
lean_dec(v_f_105_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
v___x_107_ = 1;
return v___x_107_;
}
else
{
lean_object* v_head_108_; 
v_head_108_ = lean_ctor_get(v_prf_106_, 0);
lean_inc(v_head_108_);
switch(lean_obj_tag(v_head_108_))
{
case 0:
{
lean_object* v_rupHints_109_; lean_object* v_performRupAdd_110_; lean_object* v_empty_111_; lean_object* v___x_112_; lean_object* v_snd_113_; uint8_t v___x_114_; 
lean_dec_ref(v_prf_106_);
v_rupHints_109_ = lean_ctor_get(v_head_108_, 1);
lean_inc_ref(v_rupHints_109_);
lean_dec_ref(v_head_108_);
v_performRupAdd_110_ = lean_ctor_get(v_inst_104_, 4);
lean_inc_ref(v_performRupAdd_110_);
lean_dec_ref(v_inst_104_);
v_empty_111_ = lean_ctor_get(v_inst_103_, 2);
lean_inc(v_empty_111_);
lean_dec_ref(v_inst_103_);
v___x_112_ = lean_apply_3(v_performRupAdd_110_, v_f_105_, v_empty_111_, v_rupHints_109_);
v_snd_113_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_snd_113_);
lean_dec_ref(v___x_112_);
v___x_114_ = lean_unbox(v_snd_113_);
lean_dec(v_snd_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 2;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
case 1:
{
lean_object* v_tail_117_; lean_object* v_c_118_; lean_object* v_rupHints_119_; lean_object* v_performRupAdd_120_; lean_object* v___x_121_; lean_object* v_snd_122_; uint8_t v___x_123_; 
v_tail_117_ = lean_ctor_get(v_prf_106_, 1);
lean_inc(v_tail_117_);
lean_dec_ref(v_prf_106_);
v_c_118_ = lean_ctor_get(v_head_108_, 1);
lean_inc(v_c_118_);
v_rupHints_119_ = lean_ctor_get(v_head_108_, 2);
lean_inc_ref(v_rupHints_119_);
lean_dec_ref(v_head_108_);
v_performRupAdd_120_ = lean_ctor_get(v_inst_104_, 4);
lean_inc_ref(v_performRupAdd_120_);
v___x_121_ = lean_apply_3(v_performRupAdd_120_, v_f_105_, v_c_118_, v_rupHints_119_);
v_snd_122_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_snd_122_);
v___x_123_ = lean_unbox(v_snd_122_);
lean_dec(v_snd_122_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; 
lean_dec_ref(v___x_121_);
lean_dec(v_tail_117_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
v___x_124_ = 2;
return v___x_124_;
}
else
{
lean_object* v_fst_125_; 
v_fst_125_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_fst_125_);
lean_dec_ref(v___x_121_);
v_f_105_ = v_fst_125_;
v_prf_106_ = v_tail_117_;
goto _start;
}
}
case 2:
{
lean_object* v_tail_127_; lean_object* v_c_128_; lean_object* v_pivot_129_; lean_object* v_rupHints_130_; lean_object* v_ratHints_131_; lean_object* v_performRatAdd_132_; lean_object* v___x_133_; lean_object* v_snd_134_; uint8_t v___x_135_; 
v_tail_127_ = lean_ctor_get(v_prf_106_, 1);
lean_inc(v_tail_127_);
lean_dec_ref(v_prf_106_);
v_c_128_ = lean_ctor_get(v_head_108_, 1);
lean_inc(v_c_128_);
v_pivot_129_ = lean_ctor_get(v_head_108_, 2);
lean_inc_ref(v_pivot_129_);
v_rupHints_130_ = lean_ctor_get(v_head_108_, 3);
lean_inc_ref(v_rupHints_130_);
v_ratHints_131_ = lean_ctor_get(v_head_108_, 4);
lean_inc_ref(v_ratHints_131_);
lean_dec_ref(v_head_108_);
v_performRatAdd_132_ = lean_ctor_get(v_inst_104_, 5);
lean_inc_ref(v_performRatAdd_132_);
v___x_133_ = lean_apply_5(v_performRatAdd_132_, v_f_105_, v_c_128_, v_pivot_129_, v_rupHints_130_, v_ratHints_131_);
v_snd_134_ = lean_ctor_get(v___x_133_, 1);
lean_inc(v_snd_134_);
v___x_135_ = lean_unbox(v_snd_134_);
lean_dec(v_snd_134_);
if (v___x_135_ == 0)
{
uint8_t v___x_136_; 
lean_dec_ref(v___x_133_);
lean_dec(v_tail_127_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
v___x_136_ = 2;
return v___x_136_;
}
else
{
lean_object* v_fst_137_; 
v_fst_137_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_fst_137_);
lean_dec_ref(v___x_133_);
v_f_105_ = v_fst_137_;
v_prf_106_ = v_tail_127_;
goto _start;
}
}
default: 
{
lean_object* v_tail_139_; lean_object* v_ids_140_; lean_object* v_delete_141_; lean_object* v___x_142_; 
v_tail_139_ = lean_ctor_get(v_prf_106_, 1);
lean_inc(v_tail_139_);
lean_dec_ref(v_prf_106_);
v_ids_140_ = lean_ctor_get(v_head_108_, 0);
lean_inc_ref(v_ids_140_);
lean_dec_ref(v_head_108_);
v_delete_141_ = lean_ctor_get(v_inst_104_, 3);
lean_inc(v_delete_141_);
v___x_142_ = lean_apply_2(v_delete_141_, v_f_105_, v_ids_140_);
v_f_105_ = v___x_142_;
v_prf_106_ = v_tail_139_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg___boxed(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_f_146_, lean_object* v_prf_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(v_inst_144_, v_inst_145_, v_f_146_, v_prf_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_00_u03c3_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_f_157_, lean_object* v_prf_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(v_inst_154_, v_inst_156_, v_f_157_, v_prf_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___boxed(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_00_u03c3_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_f_167_, lean_object* v_prf_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(v_00_u03b1_160_, v_00_u03b2_161_, v_00_u03c3_162_, v_inst_163_, v_inst_164_, v_inst_165_, v_inst_166_, v_f_167_, v_prf_168_);
lean_dec_ref(v_inst_163_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default();
l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult = _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
}
#ifdef __cplusplus
}
#endif
