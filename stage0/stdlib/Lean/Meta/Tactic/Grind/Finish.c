// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Finish
// Imports: public import Lean.Meta.Tactic.Grind.Action import Lean.Meta.Tactic.Grind.EMatchAction import Lean.Meta.Tactic.Grind.Split
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
lean_object* l_Lean_Meta_Grind_Action_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_splitNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mkAction();
lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_maxIterationsDefault;
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_splitNext___boxed, .m_arity = 15, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_instantiate___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_assertAll___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_intros___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_mbtc___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Action_mkFinish___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_checkTactic___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_Action_mkFinish___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkFinish___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Action_maxIterationsDefault(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(10000u);
return v___x_1_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__0(lean_object* v___f_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkFinish___lam__0___closed__0));
v___x_21_ = l_Lean_Meta_Grind_Action_orElse(v___x_20_, v___f_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
return v___x_21_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_6_ = stack[0].m_obj;
lean_object* v___y_7_ = stack[1].m_obj;
lean_object* v___y_8_ = stack[2].m_obj;
lean_object* v___y_9_ = stack[3].m_obj;
lean_object* v___y_10_ = stack[4].m_obj;
lean_object* v___y_11_ = stack[5].m_obj;
lean_object* v___y_12_ = stack[6].m_obj;
lean_object* v___y_13_ = stack[7].m_obj;
lean_object* v___y_14_ = stack[8].m_obj;
lean_object* v___y_15_ = stack[9].m_obj;
lean_object* v___y_16_ = stack[10].m_obj;
lean_object* v___y_17_ = stack[11].m_obj;
lean_object* v___y_18_ = stack[12].m_obj;
lean_object* v_res_22_;
v_res_22_ = l_Lean_Meta_Grind_Action_mkFinish___lam__0(v___f_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__0___boxed(lean_object* v___f_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_Grind_Action_mkFinish___lam__0(v___f_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
return v_res_37_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__1(lean_object* v___f_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkFinish___lam__1___closed__0));
v___x_54_ = l_Lean_Meta_Grind_Action_orElse(v___x_53_, v___f_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_39_ = stack[0].m_obj;
lean_object* v___y_40_ = stack[1].m_obj;
lean_object* v___y_41_ = stack[2].m_obj;
lean_object* v___y_42_ = stack[3].m_obj;
lean_object* v___y_43_ = stack[4].m_obj;
lean_object* v___y_44_ = stack[5].m_obj;
lean_object* v___y_45_ = stack[6].m_obj;
lean_object* v___y_46_ = stack[7].m_obj;
lean_object* v___y_47_ = stack[8].m_obj;
lean_object* v___y_48_ = stack[9].m_obj;
lean_object* v___y_49_ = stack[10].m_obj;
lean_object* v___y_50_ = stack[11].m_obj;
lean_object* v___y_51_ = stack[12].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Lean_Meta_Grind_Action_mkFinish___lam__1(v___f_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__1___boxed(lean_object* v___f_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_Grind_Action_mkFinish___lam__1(v___f_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
return v_res_70_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__2(lean_object* v_a_71_, lean_object* v___f_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_Grind_Action_orElse(v_a_71_, v___f_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_71_ = stack[0].m_obj;
lean_object* v___f_72_ = stack[1].m_obj;
lean_object* v___y_73_ = stack[2].m_obj;
lean_object* v___y_74_ = stack[3].m_obj;
lean_object* v___y_75_ = stack[4].m_obj;
lean_object* v___y_76_ = stack[5].m_obj;
lean_object* v___y_77_ = stack[6].m_obj;
lean_object* v___y_78_ = stack[7].m_obj;
lean_object* v___y_79_ = stack[8].m_obj;
lean_object* v___y_80_ = stack[9].m_obj;
lean_object* v___y_81_ = stack[10].m_obj;
lean_object* v___y_82_ = stack[11].m_obj;
lean_object* v___y_83_ = stack[12].m_obj;
lean_object* v___y_84_ = stack[13].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_Grind_Action_mkFinish___lam__2(v_a_71_, v___f_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed(lean_object* v_a_88_, lean_object* v___f_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_Grind_Action_mkFinish___lam__2(v_a_88_, v___f_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
return v_res_103_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__3(lean_object* v_maxIterations_104_, lean_object* v___f_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_Action_loop___redArg(v_maxIterations_104_, v___f_105_, v___y_106_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_maxIterations_104_ = stack[0].m_obj;
lean_object* v___f_105_ = stack[1].m_obj;
lean_object* v___y_106_ = stack[2].m_obj;
lean_object* v___y_107_ = stack[3].m_obj;
lean_object* v___y_108_ = stack[4].m_obj;
lean_object* v___y_109_ = stack[5].m_obj;
lean_object* v___y_110_ = stack[6].m_obj;
lean_object* v___y_111_ = stack[7].m_obj;
lean_object* v___y_112_ = stack[8].m_obj;
lean_object* v___y_113_ = stack[9].m_obj;
lean_object* v___y_114_ = stack[10].m_obj;
lean_object* v___y_115_ = stack[11].m_obj;
lean_object* v___y_116_ = stack[12].m_obj;
lean_object* v___y_117_ = stack[13].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_Meta_Grind_Action_mkFinish___lam__3(v_maxIterations_104_, v___f_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__3___boxed(lean_object* v_maxIterations_121_, lean_object* v___f_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_Grind_Action_mkFinish___lam__3(v_maxIterations_121_, v___f_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_124_);
lean_dec(v_maxIterations_121_);
return v_res_136_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__4(lean_object* v___f_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkFinish___lam__4___closed__0));
v___x_153_ = l_Lean_Meta_Grind_Action_andThen(v___x_152_, v___f_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_138_ = stack[0].m_obj;
lean_object* v___y_139_ = stack[1].m_obj;
lean_object* v___y_140_ = stack[2].m_obj;
lean_object* v___y_141_ = stack[3].m_obj;
lean_object* v___y_142_ = stack[4].m_obj;
lean_object* v___y_143_ = stack[5].m_obj;
lean_object* v___y_144_ = stack[6].m_obj;
lean_object* v___y_145_ = stack[7].m_obj;
lean_object* v___y_146_ = stack[8].m_obj;
lean_object* v___y_147_ = stack[9].m_obj;
lean_object* v___y_148_ = stack[10].m_obj;
lean_object* v___y_149_ = stack[11].m_obj;
lean_object* v___y_150_ = stack[12].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Meta_Grind_Action_mkFinish___lam__4(v___f_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed(lean_object* v___f_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Meta_Grind_Action_mkFinish___lam__4(v___f_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
return v_res_169_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__5(lean_object* v___f_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkFinish___lam__5___closed__0));
v___x_187_ = l_Lean_Meta_Grind_Action_andThen(v___x_186_, v___f_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_172_ = stack[0].m_obj;
lean_object* v___y_173_ = stack[1].m_obj;
lean_object* v___y_174_ = stack[2].m_obj;
lean_object* v___y_175_ = stack[3].m_obj;
lean_object* v___y_176_ = stack[4].m_obj;
lean_object* v___y_177_ = stack[5].m_obj;
lean_object* v___y_178_ = stack[6].m_obj;
lean_object* v___y_179_ = stack[7].m_obj;
lean_object* v___y_180_ = stack[8].m_obj;
lean_object* v___y_181_ = stack[9].m_obj;
lean_object* v___y_182_ = stack[10].m_obj;
lean_object* v___y_183_ = stack[11].m_obj;
lean_object* v___y_184_ = stack[12].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Lean_Meta_Grind_Action_mkFinish___lam__5(v___f_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed(lean_object* v___f_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Meta_Grind_Action_mkFinish___lam__5(v___f_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
return v_res_203_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__6(lean_object* v___x_204_, lean_object* v___f_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Grind_Action_andThen(v___x_204_, v___f_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_204_ = stack[0].m_obj;
lean_object* v___f_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v___y_207_ = stack[3].m_obj;
lean_object* v___y_208_ = stack[4].m_obj;
lean_object* v___y_209_ = stack[5].m_obj;
lean_object* v___y_210_ = stack[6].m_obj;
lean_object* v___y_211_ = stack[7].m_obj;
lean_object* v___y_212_ = stack[8].m_obj;
lean_object* v___y_213_ = stack[9].m_obj;
lean_object* v___y_214_ = stack[10].m_obj;
lean_object* v___y_215_ = stack[11].m_obj;
lean_object* v___y_216_ = stack[12].m_obj;
lean_object* v___y_217_ = stack[13].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Meta_Grind_Action_mkFinish___lam__6(v___x_204_, v___f_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed(lean_object* v___x_221_, lean_object* v___f_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_Grind_Action_mkFinish___lam__6(v___x_221_, v___f_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
return v_res_236_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkFinish(lean_object* v_maxIterations_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; 
v___f_247_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkFinish___closed__2));
v___x_248_ = l_Lean_Meta_Grind_Solvers_mkAction();
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_262_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_262_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___x_260_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mkFinish___lam__2___boxed), 15, 2);
lean_closure_set(v___f_253_, 0, v_a_249_);
lean_closure_set(v___f_253_, 1, v___f_247_);
v___f_254_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mkFinish___lam__3___boxed), 15, 2);
lean_closure_set(v___f_254_, 0, v_maxIterations_245_);
lean_closure_set(v___f_254_, 1, v___f_253_);
v___f_255_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mkFinish___lam__4___boxed), 14, 1);
lean_closure_set(v___f_255_, 0, v___f_254_);
v___f_256_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mkFinish___lam__5___boxed), 14, 1);
lean_closure_set(v___f_256_, 0, v___f_255_);
v___x_257_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkFinish___closed__3));
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mkFinish___lam__6___boxed), 15, 2);
lean_closure_set(v___f_258_, 0, v___x_257_);
lean_closure_set(v___f_258_, 1, v___f_256_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___f_258_);
v___x_260_ = v___x_251_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___f_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_dec(v_maxIterations_245_);
return v___x_248_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkFinish_0interp(lean_interpreter_value* stack)
{
lean_object* v_maxIterations_245_ = stack[0].m_obj;
lean_object* v_res_263_;
v_res_263_ = l_Lean_Meta_Grind_Action_mkFinish(v_maxIterations_245_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkFinish___boxed(lean_object* v_maxIterations_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Grind_Action_mkFinish(v_maxIterations_264_);
return v_res_266_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Action_maxIterationsDefault = _init_l_Lean_Meta_Grind_Action_maxIterationsDefault();
lean_mark_persistent(l_Lean_Meta_Grind_Action_maxIterationsDefault);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
}
#ifdef __cplusplus
}
#endif
