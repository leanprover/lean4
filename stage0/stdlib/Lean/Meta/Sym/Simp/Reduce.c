// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Reduce
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Reduce import Lean.Meta.Sym.InferType
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceBeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_beta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_beta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_beta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(lean_object* v_r_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
if (lean_obj_tag(v_r_3_) == 1)
{
lean_object* v_val_11_; lean_object* v___x_12_; 
v_val_11_ = lean_ctor_get(v_r_3_, 0);
lean_inc_n(v_val_11_, 2);
lean_dec_ref_known(v_r_3_, 1);
v___x_12_ = l_Lean_Meta_Sym_mkEqRefl(v_val_11_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_22_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_22_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_17_ = 0;
v___x_18_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_18_, 0, v_val_11_);
lean_ctor_set(v___x_18_, 1, v_a_13_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*2, v___x_17_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*2 + 1, v___x_17_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
lean_dec(v_val_11_);
v_a_23_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_12_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_12_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_r_3_);
v___x_31_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f___closed__0));
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_3_ = stack[0].m_obj;
lean_object* v_a_4_ = stack[1].m_obj;
lean_object* v_a_5_ = stack[2].m_obj;
lean_object* v_a_6_ = stack[3].m_obj;
lean_object* v_a_7_ = stack[4].m_obj;
lean_object* v_a_8_ = stack[5].m_obj;
lean_object* v_a_9_ = stack[6].m_obj;
lean_object* v_res_33_;
v_res_33_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_r_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f___boxed(lean_object* v_r_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_r_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_42_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object* v_e_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_reduceBeta_x3f(v_e_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_a_52_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
return v___x_53_;
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_54_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_51_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_51_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_beta___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_43_ = stack[0].m_obj;
lean_object* v_a_44_ = stack[1].m_obj;
lean_object* v_a_45_ = stack[2].m_obj;
lean_object* v_a_46_ = stack[3].m_obj;
lean_object* v_a_47_ = stack[4].m_obj;
lean_object* v_a_48_ = stack[5].m_obj;
lean_object* v_a_49_ = stack[6].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lean_Meta_Sym_Simp_beta___redArg(v_e_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_beta___redArg___boxed(lean_object* v_e_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_Sym_Simp_beta___redArg(v_e_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_71_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_beta(lean_object* v_e_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Meta_Sym_Simp_beta___redArg(v_e_72_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
return v___x_83_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_beta_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_72_ = stack[0].m_obj;
lean_object* v_a_73_ = stack[1].m_obj;
lean_object* v_a_74_ = stack[2].m_obj;
lean_object* v_a_75_ = stack[3].m_obj;
lean_object* v_a_76_ = stack[4].m_obj;
lean_object* v_a_77_ = stack[5].m_obj;
lean_object* v_a_78_ = stack[6].m_obj;
lean_object* v_a_79_ = stack[7].m_obj;
lean_object* v_a_80_ = stack[8].m_obj;
lean_object* v_a_81_ = stack[9].m_obj;
lean_object* v_res_84_;
v_res_84_ = l_Lean_Meta_Sym_Simp_beta(v_e_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_beta___boxed(lean_object* v_e_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Sym_Simp_beta(v_e_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
return v_res_96_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg(lean_object* v_e_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Sym_reduceZeta_x3f(v_e_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_a_106_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_105_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_105_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zeta___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_97_ = stack[0].m_obj;
lean_object* v_a_98_ = stack[1].m_obj;
lean_object* v_a_99_ = stack[2].m_obj;
lean_object* v_a_100_ = stack[3].m_obj;
lean_object* v_a_101_ = stack[4].m_obj;
lean_object* v_a_102_ = stack[5].m_obj;
lean_object* v_a_103_ = stack[6].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg___boxed(lean_object* v_e_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_125_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_zeta(lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_126_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
return v___x_137_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_126_ = stack[0].m_obj;
lean_object* v_a_127_ = stack[1].m_obj;
lean_object* v_a_128_ = stack[2].m_obj;
lean_object* v_a_129_ = stack[3].m_obj;
lean_object* v_a_130_ = stack[4].m_obj;
lean_object* v_a_131_ = stack[5].m_obj;
lean_object* v_a_132_ = stack[6].m_obj;
lean_object* v_a_133_ = stack[7].m_obj;
lean_object* v_a_134_ = stack[8].m_obj;
lean_object* v_a_135_ = stack[9].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_Meta_Sym_Simp_zeta(v_e_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zeta___boxed(lean_object* v_e_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Sym_Simp_zeta(v_e_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
return v_res_150_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg(lean_object* v_k_151_, lean_object* v_t_152_){
_start:
{
if (lean_obj_tag(v_t_152_) == 0)
{
lean_object* v_k_153_; lean_object* v_l_154_; lean_object* v_r_155_; uint8_t v___x_156_; 
v_k_153_ = lean_ctor_get(v_t_152_, 1);
v_l_154_ = lean_ctor_get(v_t_152_, 3);
v_r_155_ = lean_ctor_get(v_t_152_, 4);
v___x_156_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_151_, v_k_153_);
switch(v___x_156_)
{
case 0:
{
v_t_152_ = v_l_154_;
goto _start;
}
case 1:
{
uint8_t v___x_158_; 
v___x_158_ = 1;
return v___x_158_;
}
default: 
{
v_t_152_ = v_r_155_;
goto _start;
}
}
}
else
{
uint8_t v___x_160_; 
v___x_160_ = 0;
return v___x_160_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_151_ = stack[0].m_obj;
lean_object* v_t_152_ = stack[1].m_obj;
uint8_t v_res_161_;
v_res_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg(v_k_151_, v_t_152_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg___boxed(lean_object* v_k_162_, lean_object* v_t_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg(v_k_162_, v_t_163_);
lean_dec(v_t_163_);
lean_dec(v_k_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
uint8_t l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0(lean_object* v_s_166_, lean_object* v___y_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg(v___y_167_, v_s_166_);
return v___x_168_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_166_ = stack[0].m_obj;
lean_object* v___y_167_ = stack[1].m_obj;
uint8_t v_res_169_;
v_res_169_ = l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0(v_s_166_, v___y_167_);
stack->m_num = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0___boxed(lean_object* v_s_170_, lean_object* v___y_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0(v_s_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec(v_s_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___redArg(lean_object* v_s_174_, lean_object* v_e_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___f_183_; lean_object* v___x_184_; 
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_zetaDelta___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_183_, 0, v_s_174_);
v___x_184_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_175_, v___f_183_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v___x_186_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_a_185_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
return v___x_186_;
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_184_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zetaDelta___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_174_ = stack[0].m_obj;
lean_object* v_e_175_ = stack[1].m_obj;
lean_object* v_a_176_ = stack[2].m_obj;
lean_object* v_a_177_ = stack[3].m_obj;
lean_object* v_a_178_ = stack[4].m_obj;
lean_object* v_a_179_ = stack[5].m_obj;
lean_object* v_a_180_ = stack[6].m_obj;
lean_object* v_a_181_ = stack[7].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_Meta_Sym_Simp_zetaDelta___redArg(v_s_174_, v_e_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___redArg___boxed(lean_object* v_s_196_, lean_object* v_e_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_Sym_Simp_zetaDelta___redArg(v_s_196_, v_e_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_205_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_zetaDelta(lean_object* v_s_206_, lean_object* v_e_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Sym_Simp_zetaDelta___redArg(v_s_206_, v_e_207_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zetaDelta_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_206_ = stack[0].m_obj;
lean_object* v_e_207_ = stack[1].m_obj;
lean_object* v_a_208_ = stack[2].m_obj;
lean_object* v_a_209_ = stack[3].m_obj;
lean_object* v_a_210_ = stack[4].m_obj;
lean_object* v_a_211_ = stack[5].m_obj;
lean_object* v_a_212_ = stack[6].m_obj;
lean_object* v_a_213_ = stack[7].m_obj;
lean_object* v_a_214_ = stack[8].m_obj;
lean_object* v_a_215_ = stack[9].m_obj;
lean_object* v_a_216_ = stack[10].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Meta_Sym_Simp_zetaDelta(v_s_206_, v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDelta___boxed(lean_object* v_s_220_, lean_object* v_e_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Meta_Sym_Simp_zetaDelta(v_s_220_, v_e_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
return v_res_232_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0(lean_object* v_00_u03b2_233_, lean_object* v_k_234_, lean_object* v_t_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___redArg(v_k_234_, v_t_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_234_ = stack[1].m_obj;
lean_object* v_t_235_ = stack[2].m_obj;
uint8_t v_res_237_;
v_res_237_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0(lean_box(0), v_k_234_, v_t_235_);
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0___boxed(lean_object* v_00_u03b2_238_, lean_object* v_k_239_, lean_object* v_t_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_Simp_zetaDelta_spec__0(v_00_u03b2_238_, v_k_239_, v_t_240_);
lean_dec(v_t_240_);
lean_dec(v_k_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
uint8_t l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0(lean_object* v_x_243_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = 1;
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_243_ = stack[0].m_obj;
uint8_t v_res_245_;
v_res_245_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0(v_x_243_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0___boxed(lean_object* v_x_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___lam__0(v_x_246_);
lean_dec(v_x_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(lean_object* v_e_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___f_258_; lean_object* v___x_259_; 
v___f_258_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___closed__0));
v___x_259_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_250_, v___f_258_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
v___x_261_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_a_260_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
return v___x_261_;
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_259_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_259_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_250_ = stack[0].m_obj;
lean_object* v_a_251_ = stack[1].m_obj;
lean_object* v_a_252_ = stack[2].m_obj;
lean_object* v_a_253_ = stack[3].m_obj;
lean_object* v_a_254_ = stack[4].m_obj;
lean_object* v_a_255_ = stack[5].m_obj;
lean_object* v_a_256_ = stack[6].m_obj;
lean_object* v_res_270_;
v_res_270_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg___boxed(lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
return v_res_279_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_280_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_zetaDeltaAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_280_ = stack[0].m_obj;
lean_object* v_a_281_ = stack[1].m_obj;
lean_object* v_a_282_ = stack[2].m_obj;
lean_object* v_a_283_ = stack[3].m_obj;
lean_object* v_a_284_ = stack[4].m_obj;
lean_object* v_a_285_ = stack[5].m_obj;
lean_object* v_a_286_ = stack[6].m_obj;
lean_object* v_a_287_ = stack[7].m_obj;
lean_object* v_a_288_ = stack[8].m_obj;
lean_object* v_a_289_ = stack[9].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll(v_e_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___boxed(lean_object* v_e_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll(v_e_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
return v_res_304_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg(lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_313_, 1);
v___x_315_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_a_314_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v___x_315_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_313_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_reduceProj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_305_ = stack[0].m_obj;
lean_object* v_a_306_ = stack[1].m_obj;
lean_object* v_a_307_ = stack[2].m_obj;
lean_object* v_a_308_ = stack[3].m_obj;
lean_object* v_a_309_ = stack[4].m_obj;
lean_object* v_a_310_ = stack[5].m_obj;
lean_object* v_a_311_ = stack[6].m_obj;
lean_object* v_res_324_;
v_res_324_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v_e_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg___boxed(lean_object* v_e_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v_e_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_333_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_reduceProj(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v_e_334_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_reduceProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_334_ = stack[0].m_obj;
lean_object* v_a_335_ = stack[1].m_obj;
lean_object* v_a_336_ = stack[2].m_obj;
lean_object* v_a_337_ = stack[3].m_obj;
lean_object* v_a_338_ = stack[4].m_obj;
lean_object* v_a_339_ = stack[5].m_obj;
lean_object* v_a_340_ = stack[6].m_obj;
lean_object* v_a_341_ = stack[7].m_obj;
lean_object* v_a_342_ = stack[8].m_obj;
lean_object* v_a_343_ = stack[9].m_obj;
lean_object* v_res_346_;
v_res_346_ = l_Lean_Meta_Sym_Simp_reduceProj(v_e_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceProj___boxed(lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Sym_Simp_reduceProj(v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
return v_res_358_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = l___private_Lean_Meta_Sym_Simp_Reduce_0__Lean_Meta_Sym_Simp_ofReduce_x3f(v_a_368_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_369_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_367_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_367_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_reduceMatcher___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_359_ = stack[0].m_obj;
lean_object* v_a_360_ = stack[1].m_obj;
lean_object* v_a_361_ = stack[2].m_obj;
lean_object* v_a_362_ = stack[3].m_obj;
lean_object* v_a_363_ = stack[4].m_obj;
lean_object* v_a_364_ = stack[5].m_obj;
lean_object* v_a_365_ = stack[6].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(v_e_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___redArg___boxed(lean_object* v_e_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(v_e_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec_ref(v_e_379_);
return v_res_387_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(v_e_388_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_reduceMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_388_ = stack[0].m_obj;
lean_object* v_a_389_ = stack[1].m_obj;
lean_object* v_a_390_ = stack[2].m_obj;
lean_object* v_a_391_ = stack[3].m_obj;
lean_object* v_a_392_ = stack[4].m_obj;
lean_object* v_a_393_ = stack[5].m_obj;
lean_object* v_a_394_ = stack[6].m_obj;
lean_object* v_a_395_ = stack[7].m_obj;
lean_object* v_a_396_ = stack[8].m_obj;
lean_object* v_a_397_ = stack[9].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Meta_Sym_Simp_reduceMatcher(v_e_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Sym_Simp_reduceMatcher(v_e_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_e_401_);
return v_res_412_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
