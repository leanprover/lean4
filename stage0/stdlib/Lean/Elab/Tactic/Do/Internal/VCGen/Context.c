// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Context
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Basic public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
switch(lean_obj_tag(v_t_7_))
{
case 0:
{
return v_k_8_;
}
case 1:
{
uint8_t v_silent_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_silent_9_ = lean_ctor_get_uint8(v_t_7_, 0);
lean_dec_ref_known(v_t_7_, 0);
v___x_10_ = lean_box(v_silent_9_);
v___x_11_ = lean_apply_1(v_k_8_, v___x_10_);
return v___x_11_;
}
default: 
{
lean_object* v_tac_12_; lean_object* v___x_13_; 
v_tac_12_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_tac_12_);
lean_dec_ref_known(v_t_7_, 1);
v___x_13_ = lean_apply_1(v_k_8_, v_tac_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim___redArg(lean_object* v_t_26_, lean_object* v_none_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_26_, v_none_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_none_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_30_, v_none_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim___redArg(lean_object* v_t_34_, lean_object* v_grind_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_34_, v_grind_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_grind_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_38_, v_grind_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim___redArg(lean_object* v_t_42_, lean_object* v_tactic_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_42_, v_tactic_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_tactic_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_46_, v_tactic_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 1)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind___boxed(lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(v_x_53_);
lean_dec(v_x_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___redArg(lean_object* v_fv_56_, lean_object* v_info_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_specBackwardRuleCache_61_; lean_object* v_splitBackwardRuleCache_62_; lean_object* v_invariants_63_; lean_object* v_vcs_64_; lean_object* v_simpState_65_; lean_object* v_jps_66_; lean_object* v_fuel_67_; lean_object* v_inlineHandledInvariants_68_; uint8_t v_preTacFailed_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_80_; 
v___x_60_ = lean_st_ref_take(v_a_58_);
v_specBackwardRuleCache_61_ = lean_ctor_get(v___x_60_, 0);
v_splitBackwardRuleCache_62_ = lean_ctor_get(v___x_60_, 1);
v_invariants_63_ = lean_ctor_get(v___x_60_, 2);
v_vcs_64_ = lean_ctor_get(v___x_60_, 3);
v_simpState_65_ = lean_ctor_get(v___x_60_, 4);
v_jps_66_ = lean_ctor_get(v___x_60_, 5);
v_fuel_67_ = lean_ctor_get(v___x_60_, 6);
v_inlineHandledInvariants_68_ = lean_ctor_get(v___x_60_, 7);
v_preTacFailed_69_ = lean_ctor_get_uint8(v___x_60_, sizeof(void*)*8);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_80_ == 0)
{
v___x_71_ = v___x_60_;
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_inlineHandledInvariants_68_);
lean_inc(v_fuel_67_);
lean_inc(v_jps_66_);
lean_inc(v_simpState_65_);
lean_inc(v_vcs_64_);
lean_inc(v_invariants_63_);
lean_inc(v_splitBackwardRuleCache_62_);
lean_inc(v_specBackwardRuleCache_61_);
lean_dec(v___x_60_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_56_, v_info_57_, v_jps_66_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 5, v___x_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_specBackwardRuleCache_61_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_splitBackwardRuleCache_62_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_invariants_63_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_vcs_64_);
lean_ctor_set(v_reuseFailAlloc_79_, 4, v_simpState_65_);
lean_ctor_set(v_reuseFailAlloc_79_, 5, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 6, v_fuel_67_);
lean_ctor_set(v_reuseFailAlloc_79_, 7, v_inlineHandledInvariants_68_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*8, v_preTacFailed_69_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_st_ref_set(v_a_58_, v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___redArg___boxed(lean_object* v_fv_81_, lean_object* v_info_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___redArg(v_fv_81_, v_info_82_, v_a_83_);
lean_dec(v_a_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP(lean_object* v_fv_86_, lean_object* v_info_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___redArg(v_fv_86_, v_info_87_, v_a_89_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP___boxed(lean_object* v_fv_101_, lean_object* v_info_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_registerJP(v_fv_101_, v_info_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg(lean_object* v_t_116_, lean_object* v_k_117_){
_start:
{
if (lean_obj_tag(v_t_116_) == 0)
{
lean_object* v_k_118_; lean_object* v_v_119_; lean_object* v_l_120_; lean_object* v_r_121_; uint8_t v___x_122_; 
v_k_118_ = lean_ctor_get(v_t_116_, 1);
v_v_119_ = lean_ctor_get(v_t_116_, 2);
v_l_120_ = lean_ctor_get(v_t_116_, 3);
v_r_121_ = lean_ctor_get(v_t_116_, 4);
v___x_122_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_117_, v_k_118_);
switch(v___x_122_)
{
case 0:
{
v_t_116_ = v_l_120_;
goto _start;
}
case 1:
{
lean_object* v___x_124_; 
lean_inc(v_v_119_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v_v_119_);
return v___x_124_;
}
default: 
{
v_t_116_ = v_r_121_;
goto _start;
}
}
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_127_, lean_object* v_k_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg(v_t_127_, v_k_128_);
lean_dec(v_k_128_);
lean_dec(v_t_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___redArg(lean_object* v_fv_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v_jps_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_st_ref_get(v_a_131_);
v_jps_134_ = lean_ctor_get(v___x_133_, 5);
lean_inc(v_jps_134_);
lean_dec(v___x_133_);
v___x_135_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg(v_jps_134_, v_fv_130_);
lean_dec(v_jps_134_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___redArg___boxed(lean_object* v_fv_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___redArg(v_fv_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec(v_fv_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f(lean_object* v_fv_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___redArg(v_fv_141_, v_a_143_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f___boxed(lean_object* v_fv_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f(v_fv_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_fv_155_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0(lean_object* v_00_u03b4_169_, lean_object* v_t_170_, lean_object* v_k_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___redArg(v_t_170_, v_k_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_173_, lean_object* v_t_174_, lean_object* v_k_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_knownJP_x3f_spec__0(v_00_u03b4_173_, v_t_174_, v_k_175_);
lean_dec(v_k_175_);
lean_dec(v_t_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_fuel_180_; 
v___x_179_ = lean_st_ref_get(v_a_177_);
v_fuel_180_ = lean_ctor_get(v___x_179_, 6);
lean_inc(v_fuel_180_);
lean_dec(v___x_179_);
if (lean_obj_tag(v_fuel_180_) == 0)
{
lean_object* v_n_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_191_; 
v_n_181_ = lean_ctor_get(v_fuel_180_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_fuel_180_);
if (v_isSharedCheck_191_ == 0)
{
v___x_183_ = v_fuel_180_;
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_n_181_);
lean_dec(v_fuel_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_nat_dec_eq(v_n_181_, v___x_185_);
lean_dec(v_n_181_);
v___x_187_ = lean_box(v___x_186_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_187_);
v___x_189_ = v___x_183_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_fuel_180_);
v___x_192_ = 0;
v___x_193_ = lean_box(v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_195_);
lean_dec(v_a_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_199_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; lean_object* v_specBackwardRuleCache_227_; lean_object* v_splitBackwardRuleCache_228_; lean_object* v_invariants_229_; lean_object* v_vcs_230_; lean_object* v_simpState_231_; lean_object* v_jps_232_; lean_object* v_fuel_233_; lean_object* v_inlineHandledInvariants_234_; uint8_t v_preTacFailed_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_260_; 
v___x_226_ = lean_st_ref_take(v_a_224_);
v_specBackwardRuleCache_227_ = lean_ctor_get(v___x_226_, 0);
v_splitBackwardRuleCache_228_ = lean_ctor_get(v___x_226_, 1);
v_invariants_229_ = lean_ctor_get(v___x_226_, 2);
v_vcs_230_ = lean_ctor_get(v___x_226_, 3);
v_simpState_231_ = lean_ctor_get(v___x_226_, 4);
v_jps_232_ = lean_ctor_get(v___x_226_, 5);
v_fuel_233_ = lean_ctor_get(v___x_226_, 6);
v_inlineHandledInvariants_234_ = lean_ctor_get(v___x_226_, 7);
v_preTacFailed_235_ = lean_ctor_get_uint8(v___x_226_, sizeof(void*)*8);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_260_ == 0)
{
v___x_237_ = v___x_226_;
v_isShared_238_ = v_isSharedCheck_260_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_inlineHandledInvariants_234_);
lean_inc(v_fuel_233_);
lean_inc(v_jps_232_);
lean_inc(v_simpState_231_);
lean_inc(v_vcs_230_);
lean_inc(v_invariants_229_);
lean_inc(v_splitBackwardRuleCache_228_);
lean_inc(v_specBackwardRuleCache_227_);
lean_dec(v___x_226_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_260_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___y_241_; 
v___x_239_ = lean_box(0);
if (lean_obj_tag(v_fuel_233_) == 0)
{
lean_object* v_n_247_; lean_object* v_zero_248_; uint8_t v_isZero_249_; 
v_n_247_ = lean_ctor_get(v_fuel_233_, 0);
v_zero_248_ = lean_unsigned_to_nat(0u);
v_isZero_249_ = lean_nat_dec_eq(v_n_247_, v_zero_248_);
if (v_isZero_249_ == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_258_; 
lean_inc(v_n_247_);
v_isSharedCheck_258_ = !lean_is_exclusive(v_fuel_233_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_fuel_233_, 0);
lean_dec(v_unused_259_);
v___x_251_ = v_fuel_233_;
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_fuel_233_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_one_253_; lean_object* v_n_254_; lean_object* v___x_256_; 
v_one_253_ = lean_unsigned_to_nat(1u);
v_n_254_ = lean_nat_sub(v_n_247_, v_one_253_);
lean_dec(v_n_247_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v_n_254_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_n_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
v___y_241_ = v___x_256_;
goto v___jp_240_;
}
}
}
else
{
v___y_241_ = v_fuel_233_;
goto v___jp_240_;
}
}
else
{
v___y_241_ = v_fuel_233_;
goto v___jp_240_;
}
v___jp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 6, v___y_241_);
v___x_243_ = v___x_237_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_specBackwardRuleCache_227_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_splitBackwardRuleCache_228_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_invariants_229_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_vcs_230_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_simpState_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v_jps_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v___y_241_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_inlineHandledInvariants_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_246_, sizeof(void*)*8, v_preTacFailed_235_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_st_ref_set(v_a_224_, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_239_);
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_261_);
lean_dec(v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_265_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_289_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
}
#ifdef __cplusplus
}
#endif
