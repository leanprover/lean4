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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_st_ref_get(v_a_1_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_getScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_res_5_;
v_res_5_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_1_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg___boxed(lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_6_);
lean_dec(v_a_6_);
return v_res_8_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope(lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_9_);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_getScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_9_ = stack[0].m_obj;
lean_object* v_a_10_ = stack[1].m_obj;
lean_object* v_a_11_ = stack[2].m_obj;
lean_object* v_a_12_ = stack[3].m_obj;
lean_object* v_a_13_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Compiler_LCNF_ScopeM_getScope(v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___boxed(lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Compiler_LCNF_ScopeM_getScope(v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
return v_res_23_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(lean_object* v_newScope_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_st_ref_swap(v_a_25_, v_newScope_24_);
lean_dec(v___x_28_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_setScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_newScope_24_ = stack[0].m_obj;
lean_object* v_a_25_ = stack[1].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_24_, v_a_25_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___redArg___boxed(lean_object* v_newScope_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_31_, v_a_32_);
lean_dec(v_a_32_);
return v_res_34_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope(lean_object* v_newScope_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v_newScope_35_, v_a_36_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_setScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_newScope_35_ = stack[0].m_obj;
lean_object* v_a_36_ = stack[1].m_obj;
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_a_39_ = stack[4].m_obj;
lean_object* v_a_40_ = stack[5].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_Compiler_LCNF_ScopeM_setScope(v_newScope_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope___boxed(lean_object* v_newScope_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Compiler_LCNF_ScopeM_setScope(v_newScope_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
return v_res_51_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(lean_object* v_a_52_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_box(1);
v___x_55_ = l_Lean_Compiler_LCNF_ScopeM_setScope___redArg(v___x_54_, v_a_52_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_52_ = stack[0].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_52_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg___boxed(lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_57_);
lean_dec(v_a_57_);
return v_res_59_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope(lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(v_a_60_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_clearScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_60_ = stack[0].m_obj;
lean_object* v_a_61_ = stack[1].m_obj;
lean_object* v_a_62_ = stack[2].m_obj;
lean_object* v_a_63_ = stack[3].m_obj;
lean_object* v_a_64_ = stack[4].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Compiler_LCNF_ScopeM_clearScope(v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed(lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Compiler_LCNF_ScopeM_clearScope(v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(lean_object* v_x_75_){
_start:
{
lean_object* v_fst_76_; 
v_fst_76_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_fst_76_);
return v_fst_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0___boxed(lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__0(v_x_77_);
lean_dec_ref(v_x_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(lean_object* v___x_79_, lean_object* v_x_80_){
_start:
{
lean_inc(v___x_79_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed(lean_object* v___x_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1(v___x_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v___x_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2(lean_object* v_toFunctor_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_x_87_, lean_object* v___f_88_, lean_object* v_scope_89_){
_start:
{
lean_object* v_map_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v_y_94_; lean_object* v___x_95_; 
v_map_90_ = lean_ctor_get(v_toFunctor_84_, 0);
lean_inc(v_map_90_);
lean_dec_ref(v_toFunctor_84_);
v___x_91_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_setScope___boxed), 7, 1);
lean_closure_set(v___x_91_, 0, v_scope_89_);
v___x_92_ = lean_apply_2(v_inst_85_, lean_box(0), v___x_91_);
v___f_93_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_93_, 0, v___x_92_);
v_y_94_ = lean_apply_4(v_inst_86_, lean_box(0), lean_box(0), v_x_87_, v___f_93_);
v___x_95_ = lean_apply_4(v_map_90_, lean_box(0), lean_box(0), v___f_88_, v_y_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_toApplicative_101_; lean_object* v_toBind_102_; lean_object* v_toFunctor_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v_toApplicative_101_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_101_);
v_toBind_102_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_102_);
lean_dec_ref(v_inst_98_);
v_toFunctor_103_ = lean_ctor_get(v_toApplicative_101_, 0);
lean_inc_ref(v_toFunctor_103_);
lean_dec_ref(v_toApplicative_101_);
v___f_104_ = ((lean_object*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___closed__0));
v___x_105_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_getScope___boxed), 6, 0);
lean_inc(v_inst_97_);
v___x_106_ = lean_apply_2(v_inst_97_, lean_box(0), v___x_105_);
v___f_107_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg___lam__2), 6, 5);
lean_closure_set(v___f_107_, 0, v_toFunctor_103_);
lean_closure_set(v___f_107_, 1, v_inst_97_);
lean_closure_set(v___f_107_, 2, v_inst_99_);
lean_closure_set(v___f_107_, 3, v_x_100_);
lean_closure_set(v___f_107_, 4, v___f_104_);
v___x_108_ = lean_apply_4(v_toBind_102_, lean_box(0), lean_box(0), v___x_106_, v___f_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope(lean_object* v_m_109_, lean_object* v_00_u03b1_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(v_inst_111_, v_inst_112_, v_inst_113_, v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(lean_object* v_x_116_, lean_object* v_____r_117_){
_start:
{
lean_inc(v_x_116_);
return v_x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed(lean_object* v_x_118_, lean_object* v_____r_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0(v_x_118_, v_____r_119_);
lean_dec(v_x_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_toBind_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_toBind_125_ = lean_ctor_get(v_inst_122_, 1);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_126_, 0, v_x_124_);
v___x_127_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_clearScope___boxed), 6, 0);
lean_inc(v_inst_121_);
v___x_128_ = lean_apply_2(v_inst_121_, lean_box(0), v___x_127_);
lean_inc(v_toBind_125_);
v___x_129_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v___x_128_, v___f_126_);
v___x_130_ = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___redArg(v_inst_121_, v_inst_122_, v_inst_123_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope(lean_object* v_m_131_, lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Compiler_LCNF_ScopeM_withNewScope___redArg(v_inst_133_, v_inst_134_, v_inst_135_, v_x_136_);
return v___x_137_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(lean_object* v_k_138_, lean_object* v_t_139_){
_start:
{
if (lean_obj_tag(v_t_139_) == 0)
{
lean_object* v_k_140_; lean_object* v_l_141_; lean_object* v_r_142_; uint8_t v___x_143_; 
v_k_140_ = lean_ctor_get(v_t_139_, 1);
v_l_141_ = lean_ctor_get(v_t_139_, 3);
v_r_142_ = lean_ctor_get(v_t_139_, 4);
v___x_143_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_138_, v_k_140_);
switch(v___x_143_)
{
case 0:
{
v_t_139_ = v_l_141_;
goto _start;
}
case 1:
{
uint8_t v___x_145_; 
v___x_145_ = 1;
return v___x_145_;
}
default: 
{
v_t_139_ = v_r_142_;
goto _start;
}
}
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_138_ = stack[0].m_obj;
lean_object* v_t_139_ = stack[1].m_obj;
uint8_t v_res_148_;
v_res_148_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_138_, v_t_139_);
stack->m_num = v_res_148_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg___boxed(lean_object* v_k_149_, lean_object* v_t_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_149_, v_t_150_);
lean_dec(v_t_150_);
lean_dec(v_k_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(lean_object* v_fvarId_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_166_; 
v___x_156_ = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(v_a_154_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_166_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_166_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_166_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_fvarId_153_, v_a_157_);
lean_dec(v_a_157_);
v___x_162_ = lean_box(v___x_161_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_162_);
v___x_164_ = v___x_159_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_153_ = stack[0].m_obj;
lean_object* v_a_154_ = stack[1].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_153_, v_a_154_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg___boxed(lean_object* v_fvarId_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec(v_fvarId_168_);
return v_res_171_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope(lean_object* v_fvarId_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(v_fvarId_172_, v_a_173_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_isInScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_172_ = stack[0].m_obj;
lean_object* v_a_173_ = stack[1].m_obj;
lean_object* v_a_174_ = stack[2].m_obj;
lean_object* v_a_175_ = stack[3].m_obj;
lean_object* v_a_176_ = stack[4].m_obj;
lean_object* v_a_177_ = stack[5].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_Compiler_LCNF_ScopeM_isInScope(v_fvarId_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___boxed(lean_object* v_fvarId_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Compiler_LCNF_ScopeM_isInScope(v_fvarId_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec(v_fvarId_181_);
return v_res_188_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(lean_object* v_00_u03b2_189_, lean_object* v_k_190_, lean_object* v_t_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___redArg(v_k_190_, v_t_191_);
return v___x_192_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_190_ = stack[1].m_obj;
lean_object* v_t_191_ = stack[2].m_obj;
uint8_t v_res_193_;
v_res_193_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(lean_box(0), v_k_190_, v_t_191_);
stack->m_num = v_res_193_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0___boxed(lean_object* v_00_u03b2_194_, lean_object* v_k_195_, lean_object* v_t_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ScopeM_isInScope_spec__0(v_00_u03b2_194_, v_k_195_, v_t_196_);
lean_dec(v_t_196_);
lean_dec(v_k_195_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(lean_object* v_fvarId_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_202_ = lean_st_ref_take(v_a_200_);
v___x_203_ = lean_box(0);
v___x_204_ = l_Lean_FVarIdSet_insert(v___x_202_, v_fvarId_199_);
v___x_205_ = lean_st_ref_put(v_a_200_, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
return v___x_206_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_199_ = stack[0].m_obj;
lean_object* v_a_200_ = stack[1].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_199_, v_a_200_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg___boxed(lean_object* v_fvarId_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_208_, v_a_209_);
lean_dec(v_a_209_);
return v_res_211_;
}
}
lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope(lean_object* v_fvarId_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(v_fvarId_212_, v_a_213_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ScopeM_addToScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_212_ = stack[0].m_obj;
lean_object* v_a_213_ = stack[1].m_obj;
lean_object* v_a_214_ = stack[2].m_obj;
lean_object* v_a_215_ = stack[3].m_obj;
lean_object* v_a_216_ = stack[4].m_obj;
lean_object* v_a_217_ = stack[5].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Compiler_LCNF_ScopeM_addToScope(v_fvarId_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___boxed(lean_object* v_fvarId_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Compiler_LCNF_ScopeM_addToScope(v_fvarId_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
return v_res_228_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ScopeM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
