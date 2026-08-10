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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(lean_object* v_success_23_){
_start:
{
lean_inc(v_success_23_);
return v_success_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg___boxed(lean_object* v_success_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(v_success_24_);
lean_dec(v_success_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_success_29_){
_start:
{
lean_inc(v_success_29_);
return v_success_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_success_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_success_33_);
lean_dec(v_success_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(lean_object* v_outOfProof_36_){
_start:
{
lean_inc(v_outOfProof_36_);
return v_outOfProof_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg___boxed(lean_object* v_outOfProof_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(v_outOfProof_37_);
lean_dec(v_outOfProof_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_outOfProof_42_){
_start:
{
lean_inc(v_outOfProof_42_);
return v_outOfProof_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_outOfProof_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_outOfProof_46_);
lean_dec(v_outOfProof_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(lean_object* v_rupFailure_49_){
_start:
{
lean_inc(v_rupFailure_49_);
return v_rupFailure_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg___boxed(lean_object* v_rupFailure_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(v_rupFailure_50_);
lean_dec(v_rupFailure_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_rupFailure_55_){
_start:
{
lean_inc(v_rupFailure_55_);
return v_rupFailure_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_rupFailure_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_rupFailure_59_);
lean_dec(v_rupFailure_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(lean_object* v_n_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_dec_le(v_n_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_dec_le(v_n_64_, v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 2;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat___boxed(lean_object* v_n_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(v_n_72_);
lean_dec(v_n_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_75_);
v___x_78_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_x_13__boxed_82_; uint8_t v_y_14__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_x_13__boxed_82_ = lean_unbox(v_x_80_);
v_y_14__boxed_83_ = lean_unbox(v_y_81_);
v_res_84_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(v_x_13__boxed_82_, v_y_14__boxed_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(uint8_t v_x_89_){
_start:
{
switch(v_x_89_)
{
case 0:
{
lean_object* v___x_90_; 
v___x_90_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0));
return v___x_90_;
}
case 1:
{
lean_object* v___x_91_; 
v___x_91_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1));
return v___x_91_;
}
default: 
{
lean_object* v___x_92_; 
v___x_92_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2));
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_x_36__boxed_94_; lean_object* v_res_95_; 
v_x_36__boxed_94_ = lean_unbox(v_x_93_);
v_res_95_ = l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(v_x_36__boxed_94_);
return v_res_95_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_f_100_, lean_object* v_prf_101_){
_start:
{
if (lean_obj_tag(v_prf_101_) == 0)
{
uint8_t v___x_102_; 
lean_dec(v_f_100_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
v___x_102_ = 1;
return v___x_102_;
}
else
{
lean_object* v_head_103_; 
v_head_103_ = lean_ctor_get(v_prf_101_, 0);
lean_inc(v_head_103_);
switch(lean_obj_tag(v_head_103_))
{
case 0:
{
lean_object* v_rupHints_104_; lean_object* v_performRupAdd_105_; lean_object* v_empty_106_; lean_object* v___x_107_; lean_object* v_snd_108_; uint8_t v___x_109_; 
lean_dec_ref_known(v_prf_101_, 2);
v_rupHints_104_ = lean_ctor_get(v_head_103_, 1);
lean_inc_ref(v_rupHints_104_);
lean_dec_ref_known(v_head_103_, 2);
v_performRupAdd_105_ = lean_ctor_get(v_inst_99_, 4);
lean_inc_ref(v_performRupAdd_105_);
lean_dec_ref(v_inst_99_);
v_empty_106_ = lean_ctor_get(v_inst_98_, 2);
lean_inc(v_empty_106_);
lean_dec_ref(v_inst_98_);
v___x_107_ = lean_apply_3(v_performRupAdd_105_, v_f_100_, v_empty_106_, v_rupHints_104_);
v_snd_108_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_snd_108_);
lean_dec_ref(v___x_107_);
v___x_109_ = lean_unbox(v_snd_108_);
lean_dec(v_snd_108_);
if (v___x_109_ == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 2;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
case 1:
{
lean_object* v_tail_112_; lean_object* v_c_113_; lean_object* v_rupHints_114_; lean_object* v_performRupAdd_115_; lean_object* v___x_116_; lean_object* v_snd_117_; uint8_t v___x_118_; 
v_tail_112_ = lean_ctor_get(v_prf_101_, 1);
lean_inc(v_tail_112_);
lean_dec_ref_known(v_prf_101_, 2);
v_c_113_ = lean_ctor_get(v_head_103_, 1);
lean_inc(v_c_113_);
v_rupHints_114_ = lean_ctor_get(v_head_103_, 2);
lean_inc_ref(v_rupHints_114_);
lean_dec_ref_known(v_head_103_, 3);
v_performRupAdd_115_ = lean_ctor_get(v_inst_99_, 4);
lean_inc_ref(v_performRupAdd_115_);
v___x_116_ = lean_apply_3(v_performRupAdd_115_, v_f_100_, v_c_113_, v_rupHints_114_);
v_snd_117_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_snd_117_);
v___x_118_ = lean_unbox(v_snd_117_);
lean_dec(v_snd_117_);
if (v___x_118_ == 0)
{
uint8_t v___x_119_; 
lean_dec_ref(v___x_116_);
lean_dec(v_tail_112_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
v___x_119_ = 2;
return v___x_119_;
}
else
{
lean_object* v_fst_120_; 
v_fst_120_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_fst_120_);
lean_dec_ref(v___x_116_);
v_f_100_ = v_fst_120_;
v_prf_101_ = v_tail_112_;
goto _start;
}
}
case 2:
{
lean_object* v_tail_122_; lean_object* v_c_123_; lean_object* v_pivot_124_; lean_object* v_rupHints_125_; lean_object* v_ratHints_126_; lean_object* v_performRatAdd_127_; lean_object* v___x_128_; lean_object* v_snd_129_; uint8_t v___x_130_; 
v_tail_122_ = lean_ctor_get(v_prf_101_, 1);
lean_inc(v_tail_122_);
lean_dec_ref_known(v_prf_101_, 2);
v_c_123_ = lean_ctor_get(v_head_103_, 1);
lean_inc(v_c_123_);
v_pivot_124_ = lean_ctor_get(v_head_103_, 2);
lean_inc_ref(v_pivot_124_);
v_rupHints_125_ = lean_ctor_get(v_head_103_, 3);
lean_inc_ref(v_rupHints_125_);
v_ratHints_126_ = lean_ctor_get(v_head_103_, 4);
lean_inc_ref(v_ratHints_126_);
lean_dec_ref_known(v_head_103_, 5);
v_performRatAdd_127_ = lean_ctor_get(v_inst_99_, 5);
lean_inc_ref(v_performRatAdd_127_);
v___x_128_ = lean_apply_5(v_performRatAdd_127_, v_f_100_, v_c_123_, v_pivot_124_, v_rupHints_125_, v_ratHints_126_);
v_snd_129_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_snd_129_);
v___x_130_ = lean_unbox(v_snd_129_);
lean_dec(v_snd_129_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
lean_dec_ref(v___x_128_);
lean_dec(v_tail_122_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
v___x_131_ = 2;
return v___x_131_;
}
else
{
lean_object* v_fst_132_; 
v_fst_132_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v___x_128_);
v_f_100_ = v_fst_132_;
v_prf_101_ = v_tail_122_;
goto _start;
}
}
default: 
{
lean_object* v_tail_134_; lean_object* v_ids_135_; lean_object* v_delete_136_; lean_object* v___x_137_; 
v_tail_134_ = lean_ctor_get(v_prf_101_, 1);
lean_inc(v_tail_134_);
lean_dec_ref_known(v_prf_101_, 2);
v_ids_135_ = lean_ctor_get(v_head_103_, 0);
lean_inc_ref(v_ids_135_);
lean_dec_ref_known(v_head_103_, 1);
v_delete_136_ = lean_ctor_get(v_inst_99_, 3);
lean_inc(v_delete_136_);
v___x_137_ = lean_apply_2(v_delete_136_, v_f_100_, v_ids_135_);
v_f_100_ = v___x_137_;
v_prf_101_ = v_tail_134_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg___boxed(lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_f_141_, lean_object* v_prf_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(v_inst_139_, v_inst_140_, v_f_141_, v_prf_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_00_u03c3_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_f_152_, lean_object* v_prf_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(v_inst_149_, v_inst_151_, v_f_152_, v_prf_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___boxed(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_00_u03c3_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_f_162_, lean_object* v_prf_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(v_00_u03b1_155_, v_00_u03b2_156_, v_00_u03c3_157_, v_inst_158_, v_inst_159_, v_inst_160_, v_inst_161_, v_f_162_, v_prf_163_);
lean_dec_ref(v_inst_158_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
