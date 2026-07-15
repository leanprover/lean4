// Lean compiler output
// Module: Lean.Compiler.LCNF.ScopeM
// Imports: public import Lean.Compiler.LCNF.CompilerM
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_st_ref_get(v_a_1_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg___boxed(lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_5_);
lean_dec(v_a_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope(lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_8_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___boxed(lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Compiler_LCNF_ScopeM_getScope(v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_15_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(lean_object* v_newScope_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_st_ref_set(v_a_23_, v_newScope_22_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___redArg___boxed(lean_object* v_newScope_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_27_, v_a_28_);
lean_dec(v_a_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope(lean_object* v_newScope_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_31_, v_a_32_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___boxed(lean_object* v_newScope_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Compiler_LCNF_ScopeM_setScope(v_newScope_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_box(1);
v___x_50_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v___x_49_, v_a_47_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg___boxed(lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_51_);
lean_dec(v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope(lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed(lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Compiler_LCNF_ScopeM_clearScope(v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(lean_object* v_x_68_){
_start:
{
lean_object* v_fst_69_; 
v_fst_69_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_fst_69_);
return v_fst_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed(lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(v_x_70_);
lean_dec_ref(v_x_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(lean_object* v___x_72_, lean_object* v_x_73_){
_start:
{
lean_inc(v___x_72_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed(lean_object* v___x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(v___x_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v___x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2(lean_object* v_toFunctor_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_x_80_, lean_object* v___f_81_, lean_object* v_scope_82_){
_start:
{
lean_object* v_map_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___f_86_; lean_object* v_y_87_; lean_object* v___x_88_; 
v_map_83_ = lean_ctor_get(v_toFunctor_77_, 0);
lean_inc(v_map_83_);
lean_dec_ref(v_toFunctor_77_);
v___x_84_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_setScope___boxed), 7, 1);
lean_closure_set(v___x_84_, 0, v_scope_82_);
v___x_85_ = lean_apply_2(v_inst_78_, lean_box(0), v___x_84_);
v___f_86_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_86_, 0, v___x_85_);
v_y_87_ = lean_apply_4(v_inst_79_, lean_box(0), lean_box(0), v_x_80_, v___f_86_);
v___x_88_ = lean_apply_4(v_map_83_, lean_box(0), lean_box(0), v___f_81_, v_y_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_toApplicative_94_; lean_object* v_toBind_95_; lean_object* v_toFunctor_96_; lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
v_toApplicative_94_ = lean_ctor_get(v_inst_91_, 0);
lean_inc_ref(v_toApplicative_94_);
v_toBind_95_ = lean_ctor_get(v_inst_91_, 1);
lean_inc(v_toBind_95_);
lean_dec_ref(v_inst_91_);
v_toFunctor_96_ = lean_ctor_get(v_toApplicative_94_, 0);
lean_inc_ref(v_toFunctor_96_);
lean_dec_ref(v_toApplicative_94_);
v___f_97_ = ((lean_object*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0));
v___x_98_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_getScope___boxed), 6, 0);
lean_inc(v_inst_90_);
v___x_99_ = lean_apply_2(v_inst_90_, lean_box(0), v___x_98_);
v___f_100_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2), 6, 5);
lean_closure_set(v___f_100_, 0, v_toFunctor_96_);
lean_closure_set(v___f_100_, 1, v_inst_90_);
lean_closure_set(v___f_100_, 2, v_inst_92_);
lean_closure_set(v___f_100_, 3, v_x_93_);
lean_closure_set(v___f_100_, 4, v___f_97_);
v___x_101_ = lean_apply_4(v_toBind_95_, lean_box(0), lean_box(0), v___x_99_, v___f_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope(lean_object* v_m_102_, lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(v_inst_104_, v_inst_105_, v_inst_106_, v_x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(lean_object* v_x_109_, lean_object* v_____r_110_){
_start:
{
lean_inc(v_x_109_);
return v_x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed(lean_object* v_x_111_, lean_object* v_____r_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(v_x_111_, v_____r_112_);
lean_dec(v_x_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_toBind_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_toBind_118_ = lean_ctor_get(v_inst_115_, 1);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v_x_117_);
v___x_120_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed), 6, 0);
lean_inc(v_inst_114_);
v___x_121_ = lean_apply_2(v_inst_114_, lean_box(0), v___x_120_);
lean_inc(v_toBind_118_);
v___x_122_ = lean_apply_4(v_toBind_118_, lean_box(0), lean_box(0), v___x_121_, v___f_119_);
v___x_123_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(v_inst_114_, v_inst_115_, v_inst_116_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope(lean_object* v_m_124_, lean_object* v_00_u03b1_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(v_inst_126_, v_inst_127_, v_inst_128_, v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(lean_object* v_k_131_, lean_object* v_t_132_){
_start:
{
if (lean_obj_tag(v_t_132_) == 0)
{
lean_object* v_k_133_; lean_object* v_l_134_; lean_object* v_r_135_; uint8_t v___x_136_; 
v_k_133_ = lean_ctor_get(v_t_132_, 1);
v_l_134_ = lean_ctor_get(v_t_132_, 3);
v_r_135_ = lean_ctor_get(v_t_132_, 4);
v___x_136_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_131_, v_k_133_);
switch(v___x_136_)
{
case 0:
{
v_t_132_ = v_l_134_;
goto _start;
}
case 1:
{
uint8_t v___x_138_; 
v___x_138_ = 1;
return v___x_138_;
}
default: 
{
v_t_132_ = v_r_135_;
goto _start;
}
}
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg___boxed(lean_object* v_k_141_, lean_object* v_t_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_141_, v_t_142_);
lean_dec(v_t_142_);
lean_dec(v_k_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(lean_object* v_fvarId_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_158_; 
v___x_148_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_146_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_158_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_153_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_fvarId_145_, v_a_149_);
lean_dec(v_a_149_);
v___x_154_ = lean_box(v___x_153_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_154_);
v___x_156_ = v___x_151_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg___boxed(lean_object* v_fvarId_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec(v_fvarId_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope(lean_object* v_fvarId_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_163_, v_a_164_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___boxed(lean_object* v_fvarId_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Compiler_LCNF_ScopeM_isInScope(v_fvarId_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_fvarId_171_);
return v_res_178_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(lean_object* v_00_u03b2_179_, lean_object* v_k_180_, lean_object* v_t_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_180_, v_t_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___boxed(lean_object* v_00_u03b2_183_, lean_object* v_k_184_, lean_object* v_t_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(v_00_u03b2_183_, v_k_184_, v_t_185_);
lean_dec(v_t_185_);
lean_dec(v_k_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(lean_object* v_fvarId_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_191_ = lean_st_ref_take(v_a_189_);
v___x_192_ = l_Lean_FVarIdSet_insert(v___x_191_, v_fvarId_188_);
v___x_193_ = lean_st_ref_set(v_a_189_, v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg___boxed(lean_object* v_fvarId_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_196_, v_a_197_);
lean_dec(v_a_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope(lean_object* v_fvarId_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_200_, v_a_201_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___boxed(lean_object* v_fvarId_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Compiler_LCNF_ScopeM_addToScope(v_fvarId_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
return v_res_215_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ScopeM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ScopeM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ScopeM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ScopeM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ScopeM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ScopeM(builtin);
}
#ifdef __cplusplus
}
#endif
