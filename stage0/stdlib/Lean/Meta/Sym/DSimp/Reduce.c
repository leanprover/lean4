// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Reduce
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.Reduce import Lean.Meta.WHNF
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceBeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_reduceZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(lean_object* v_r_3_){
_start:
{
if (lean_obj_tag(v_r_3_) == 0)
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0));
return v___x_4_;
}
else
{
lean_object* v_val_5_; uint8_t v___x_6_; lean_object* v___x_7_; 
v_val_5_ = lean_ctor_get(v_r_3_, 0);
v___x_6_ = 0;
lean_inc(v_val_5_);
v___x_7_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_7_, 0, v_val_5_);
lean_ctor_set_uint8(v___x_7_, sizeof(void*)*1, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___boxed(lean_object* v_r_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_r_8_);
lean_dec(v_r_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object* v_e_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Sym_reduceBeta_x3f(v_e_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_27_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_27_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_19_);
lean_dec(v_a_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_23_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_a_28_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_18_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_18_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object* v_e_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object* v_e_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_45_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object* v_e_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Sym_DSimp_beta(v_e_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
return v_res_68_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(lean_object* v_k_69_, lean_object* v_t_70_){
_start:
{
if (lean_obj_tag(v_t_70_) == 0)
{
lean_object* v_k_71_; lean_object* v_l_72_; lean_object* v_r_73_; uint8_t v___x_74_; 
v_k_71_ = lean_ctor_get(v_t_70_, 1);
v_l_72_ = lean_ctor_get(v_t_70_, 3);
v_r_73_ = lean_ctor_get(v_t_70_, 4);
v___x_74_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_69_, v_k_71_);
switch(v___x_74_)
{
case 0:
{
v_t_70_ = v_l_72_;
goto _start;
}
case 1:
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
default: 
{
v_t_70_ = v_r_73_;
goto _start;
}
}
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg___boxed(lean_object* v_k_79_, lean_object* v_t_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_79_, v_t_80_);
lean_dec(v_t_80_);
lean_dec(v_k_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0(lean_object* v_s_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v___y_84_, v_s_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0___boxed(lean_object* v_s_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0(v_s_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec(v_s_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object* v_s_90_, lean_object* v_e_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; 
v___f_99_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_99_, 0, v_s_90_);
v___x_100_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_91_, v___f_99_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_101_);
lean_dec(v_a_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_100_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___boxed(lean_object* v_s_118_, lean_object* v_e_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_118_, v_e_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta(lean_object* v_s_128_, lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_128_, v_e_129_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___boxed(lean_object* v_s_141_, lean_object* v_e_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Meta_Sym_DSimp_zetaDelta(v_s_141_, v_e_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
return v_res_153_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(lean_object* v_00_u03b2_154_, lean_object* v_k_155_, lean_object* v_t_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_155_, v_t_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___boxed(lean_object* v_00_u03b2_158_, lean_object* v_k_159_, lean_object* v_t_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(v_00_u03b2_158_, v_k_159_, v_t_160_);
lean_dec(v_t_160_);
lean_dec(v_k_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0(lean_object* v_x_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0___boxed(lean_object* v_x_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0(v_x_165_);
lean_dec(v_x_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; 
v___f_177_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___closed__0));
v___x_178_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_169_, v___f_177_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_179_);
lean_dec(v_a_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_178_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_178_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___boxed(lean_object* v_e_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll(lean_object* v_e_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_205_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed(lean_object* v_e_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll(v_e_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object* v_e_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Sym_reduceZeta_x3f(v_e_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_246_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_238_);
lean_dec(v_a_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_237_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_237_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object* v_e_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object* v_e_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_264_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Sym_DSimp_zeta(v_e_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_297_);
lean_dec(v_a_297_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_a_306_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_296_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_296_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg___boxed(lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object* v_e_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_323_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object* v_e_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v_e_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_364_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_356_);
lean_dec(v_a_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_a_365_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_355_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_355_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_e_373_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object* v_e_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_382_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Sym_DSimp_dsimpMatch(v_e_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_e_394_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___redArg(lean_object* v_declNames_406_, lean_object* v_e_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Expr_getAppFn(v_e_407_);
if (lean_obj_tag(v___x_415_) == 4)
{
lean_object* v_declName_416_; uint8_t v___x_417_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; 
v_declName_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_declName_416_);
lean_dec_ref_known(v___x_415_, 2);
v___x_417_ = l_Lean_NameSet_contains(v_declNames_406_, v_declName_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_declName_416_);
lean_dec_ref(v_e_407_);
v___x_463_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_463_, 0, v___x_417_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v_env_466_; uint8_t v___x_467_; 
v___x_465_ = lean_st_ref_get(v_a_413_);
v_env_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref_n(v_env_466_, 2);
lean_dec(v___x_465_);
lean_inc(v_declName_416_);
v___x_467_ = l_Lean_Meta_hasSmartUnfoldingDecl(v_env_466_, v_declName_416_);
if (v___x_467_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Environment_find_x3f(v_env_466_, v_declName_416_, v___x_467_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec_ref(v_e_407_);
goto v___jp_468_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; 
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = l_Lean_ConstantInfo_value_x3f(v_val_472_, v___x_467_);
if (lean_obj_tag(v___x_473_) == 1)
{
lean_object* v_val_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
v_val_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_485_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_val_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = l_Lean_Expr_getAppNumArgs(v_e_407_);
v___x_479_ = l_Lean_Expr_getNumHeadLambdas(v_val_474_);
lean_dec(v_val_474_);
v___x_480_ = lean_nat_dec_lt(v___x_478_, v___x_479_);
lean_dec(v___x_479_);
lean_dec(v___x_478_);
if (v___x_480_ == 0)
{
lean_del_object(v___x_476_);
v___y_419_ = v_a_408_;
v___y_420_ = v_a_409_;
v___y_421_ = v_a_410_;
v___y_422_ = v_a_411_;
v___y_423_ = v_a_412_;
v___y_424_ = v_a_413_;
goto v___jp_418_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec_ref(v_e_407_);
v___x_481_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_481_, 0, v___x_467_);
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 0);
lean_ctor_set(v___x_476_, 0, v___x_481_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_dec(v___x_473_);
lean_dec_ref(v_e_407_);
goto v___jp_468_;
}
}
}
else
{
lean_dec_ref(v_env_466_);
lean_dec(v_declName_416_);
v___y_419_ = v_a_408_;
v___y_420_ = v_a_409_;
v___y_421_ = v_a_410_;
v___y_422_ = v_a_411_;
v___y_423_ = v_a_412_;
v___y_424_ = v_a_413_;
goto v___jp_418_;
}
v___jp_468_:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_469_, 0, v___x_467_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
v___jp_418_:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_407_, v___x_417_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_454_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_454_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_454_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_454_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 1)
{
lean_object* v_val_430_; lean_object* v___x_431_; 
lean_del_object(v___x_428_);
v_val_430_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_a_426_, 1);
v___x_431_ = l_Lean_Meta_Sym_shareCommon(v_val_430_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = 0;
v___x_437_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_437_, 0, v_a_432_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*1, v___x_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_431_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_431_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec(v_a_426_);
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0));
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_450_);
v___x_452_ = v___x_428_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_425_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_425_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec_ref(v___x_415_);
lean_dec_ref(v_e_407_);
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0));
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___redArg___boxed(lean_object* v_declNames_488_, lean_object* v_e_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Meta_Sym_DSimp_unfold___redArg(v_declNames_488_, v_e_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_declNames_488_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold(lean_object* v_declNames_498_, lean_object* v_e_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_Sym_DSimp_unfold___redArg(v_declNames_498_, v_e_499_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___boxed(lean_object* v_declNames_511_, lean_object* v_e_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_Sym_DSimp_unfold(v_declNames_511_, v_e_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec(v_declNames_511_);
return v_res_523_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
