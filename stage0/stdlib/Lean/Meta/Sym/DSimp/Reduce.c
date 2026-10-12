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
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object* v_e_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_beta___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_10_ = stack[0].m_obj;
lean_object* v_a_11_ = stack[1].m_obj;
lean_object* v_a_12_ = stack[2].m_obj;
lean_object* v_a_13_ = stack[3].m_obj;
lean_object* v_a_14_ = stack[4].m_obj;
lean_object* v_a_15_ = stack[5].m_obj;
lean_object* v_a_16_ = stack[6].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object* v_e_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
return v_res_45_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_46_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_57_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_beta_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_46_ = stack[0].m_obj;
lean_object* v_a_47_ = stack[1].m_obj;
lean_object* v_a_48_ = stack[2].m_obj;
lean_object* v_a_49_ = stack[3].m_obj;
lean_object* v_a_50_ = stack[4].m_obj;
lean_object* v_a_51_ = stack[5].m_obj;
lean_object* v_a_52_ = stack[6].m_obj;
lean_object* v_a_53_ = stack[7].m_obj;
lean_object* v_a_54_ = stack[8].m_obj;
lean_object* v_a_55_ = stack[9].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_Lean_Meta_Sym_DSimp_beta(v_e_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object* v_e_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_Sym_DSimp_beta(v_e_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
return v_res_70_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(lean_object* v_k_71_, lean_object* v_t_72_){
_start:
{
if (lean_obj_tag(v_t_72_) == 0)
{
lean_object* v_k_73_; lean_object* v_l_74_; lean_object* v_r_75_; uint8_t v___x_76_; 
v_k_73_ = lean_ctor_get(v_t_72_, 1);
v_l_74_ = lean_ctor_get(v_t_72_, 3);
v_r_75_ = lean_ctor_get(v_t_72_, 4);
v___x_76_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_71_, v_k_73_);
switch(v___x_76_)
{
case 0:
{
v_t_72_ = v_l_74_;
goto _start;
}
case 1:
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
default: 
{
v_t_72_ = v_r_75_;
goto _start;
}
}
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_71_ = stack[0].m_obj;
lean_object* v_t_72_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_71_, v_t_72_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg___boxed(lean_object* v_k_82_, lean_object* v_t_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_82_, v_t_83_);
lean_dec(v_t_83_);
lean_dec(v_k_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint8_t l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0(lean_object* v_s_86_, lean_object* v___y_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v___y_87_, v_s_86_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_86_ = stack[0].m_obj;
lean_object* v___y_87_ = stack[1].m_obj;
uint8_t v_res_89_;
v_res_89_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0(v_s_86_, v___y_87_);
stack->m_num = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0___boxed(lean_object* v_s_90_, lean_object* v___y_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0(v_s_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec(v_s_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object* v_s_94_, lean_object* v_e_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___f_103_; lean_object* v___x_104_; 
v___f_103_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_103_, 0, v_s_94_);
v___x_104_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_95_, v___f_103_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_113_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_105_);
lean_dec(v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_104_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zetaDelta___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_94_ = stack[0].m_obj;
lean_object* v_e_95_ = stack[1].m_obj;
lean_object* v_a_96_ = stack[2].m_obj;
lean_object* v_a_97_ = stack[3].m_obj;
lean_object* v_a_98_ = stack[4].m_obj;
lean_object* v_a_99_ = stack[5].m_obj;
lean_object* v_a_100_ = stack[6].m_obj;
lean_object* v_a_101_ = stack[7].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_94_, v_e_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___boxed(lean_object* v_s_123_, lean_object* v_e_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_123_, v_e_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
return v_res_132_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta(lean_object* v_s_133_, lean_object* v_e_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_133_, v_e_134_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
return v___x_145_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zetaDelta_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_133_ = stack[0].m_obj;
lean_object* v_e_134_ = stack[1].m_obj;
lean_object* v_a_135_ = stack[2].m_obj;
lean_object* v_a_136_ = stack[3].m_obj;
lean_object* v_a_137_ = stack[4].m_obj;
lean_object* v_a_138_ = stack[5].m_obj;
lean_object* v_a_139_ = stack[6].m_obj;
lean_object* v_a_140_ = stack[7].m_obj;
lean_object* v_a_141_ = stack[8].m_obj;
lean_object* v_a_142_ = stack[9].m_obj;
lean_object* v_a_143_ = stack[10].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_Lean_Meta_Sym_DSimp_zetaDelta(v_s_133_, v_e_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___boxed(lean_object* v_s_147_, lean_object* v_e_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_Sym_DSimp_zetaDelta(v_s_147_, v_e_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
return v_res_159_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(lean_object* v_00_u03b2_160_, lean_object* v_k_161_, lean_object* v_t_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_161_, v_t_162_);
return v___x_163_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_161_ = stack[1].m_obj;
lean_object* v_t_162_ = stack[2].m_obj;
uint8_t v_res_164_;
v_res_164_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(lean_box(0), v_k_161_, v_t_162_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___boxed(lean_object* v_00_u03b2_165_, lean_object* v_k_166_, lean_object* v_t_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(v_00_u03b2_165_, v_k_166_, v_t_167_);
lean_dec(v_t_167_);
lean_dec(v_k_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
uint8_t l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0(lean_object* v_x_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = 1;
return v___x_171_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_170_ = stack[0].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0(v_x_170_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0___boxed(lean_object* v_x_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___lam__0(v_x_173_);
lean_dec(v_x_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___f_185_; lean_object* v___x_186_; 
v___f_185_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___closed__0));
v___x_186_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_177_, v___f_185_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_187_);
lean_dec(v_a_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_186_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_186_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_177_ = stack[0].m_obj;
lean_object* v_a_178_ = stack[1].m_obj;
lean_object* v_a_179_ = stack[2].m_obj;
lean_object* v_a_180_ = stack[3].m_obj;
lean_object* v_a_181_ = stack[4].m_obj;
lean_object* v_a_182_ = stack[5].m_obj;
lean_object* v_a_183_ = stack[6].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___boxed(lean_object* v_e_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_213_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll(lean_object* v_e_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_214_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
return v___x_225_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zetaDeltaAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_214_ = stack[0].m_obj;
lean_object* v_a_215_ = stack[1].m_obj;
lean_object* v_a_216_ = stack[2].m_obj;
lean_object* v_a_217_ = stack[3].m_obj;
lean_object* v_a_218_ = stack[4].m_obj;
lean_object* v_a_219_ = stack[5].m_obj;
lean_object* v_a_220_ = stack[6].m_obj;
lean_object* v_a_221_ = stack[7].m_obj;
lean_object* v_a_222_ = stack[8].m_obj;
lean_object* v_a_223_ = stack[9].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll(v_e_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed(lean_object* v_e_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll(v_e_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
return v_res_238_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object* v_e_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Sym_reduceZeta_x3f(v_e_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_248_);
lean_dec(v_a_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_247_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_247_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zeta___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_239_ = stack[0].m_obj;
lean_object* v_a_240_ = stack[1].m_obj;
lean_object* v_a_241_ = stack[2].m_obj;
lean_object* v_a_242_ = stack[3].m_obj;
lean_object* v_a_243_ = stack[4].m_obj;
lean_object* v_a_244_ = stack[5].m_obj;
lean_object* v_a_245_ = stack[6].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_274_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object* v_e_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_275_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_zeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_275_ = stack[0].m_obj;
lean_object* v_a_276_ = stack[1].m_obj;
lean_object* v_a_277_ = stack[2].m_obj;
lean_object* v_a_278_ = stack[3].m_obj;
lean_object* v_a_279_ = stack[4].m_obj;
lean_object* v_a_280_ = stack[5].m_obj;
lean_object* v_a_281_ = stack[6].m_obj;
lean_object* v_a_282_ = stack[7].m_obj;
lean_object* v_a_283_ = stack[8].m_obj;
lean_object* v_a_284_ = stack[9].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_Lean_Meta_Sym_DSimp_zeta(v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Sym_DSimp_zeta(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
return v_res_299_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(lean_object* v_e_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_309_);
lean_dec(v_a_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_a_318_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_308_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_308_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpProj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_300_ = stack[0].m_obj;
lean_object* v_a_301_ = stack[1].m_obj;
lean_object* v_a_302_ = stack[2].m_obj;
lean_object* v_a_303_ = stack[3].m_obj;
lean_object* v_a_304_ = stack[4].m_obj;
lean_object* v_a_305_ = stack[5].m_obj;
lean_object* v_a_306_ = stack[6].m_obj;
lean_object* v_res_326_;
v_res_326_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg___boxed(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_335_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_336_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_336_ = stack[0].m_obj;
lean_object* v_a_337_ = stack[1].m_obj;
lean_object* v_a_338_ = stack[2].m_obj;
lean_object* v_a_339_ = stack[3].m_obj;
lean_object* v_a_340_ = stack[4].m_obj;
lean_object* v_a_341_ = stack[5].m_obj;
lean_object* v_a_342_ = stack[6].m_obj;
lean_object* v_a_343_ = stack[7].m_obj;
lean_object* v_a_344_ = stack[8].m_obj;
lean_object* v_a_345_ = stack[9].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v_e_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v_e_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
return v_res_360_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object* v_e_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_378_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f(v_a_370_);
lean_dec(v_a_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_369_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_369_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_361_ = stack[0].m_obj;
lean_object* v_a_362_ = stack[1].m_obj;
lean_object* v_a_363_ = stack[2].m_obj;
lean_object* v_a_364_ = stack[3].m_obj;
lean_object* v_a_365_ = stack[4].m_obj;
lean_object* v_a_366_ = stack[5].m_obj;
lean_object* v_a_367_ = stack[6].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec_ref(v_e_388_);
return v_res_396_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_397_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_408_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_397_ = stack[0].m_obj;
lean_object* v_a_398_ = stack[1].m_obj;
lean_object* v_a_399_ = stack[2].m_obj;
lean_object* v_a_400_ = stack[3].m_obj;
lean_object* v_a_401_ = stack[4].m_obj;
lean_object* v_a_402_ = stack[5].m_obj;
lean_object* v_a_403_ = stack[6].m_obj;
lean_object* v_a_404_ = stack[7].m_obj;
lean_object* v_a_405_ = stack[8].m_obj;
lean_object* v_a_406_ = stack[9].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Lean_Meta_Sym_DSimp_dsimpMatch(v_e_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Sym_DSimp_dsimpMatch(v_e_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_e_410_);
return v_res_421_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_unfold___redArg(lean_object* v_declNames_422_, lean_object* v_e_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Expr_getAppFn(v_e_423_);
if (lean_obj_tag(v___x_431_) == 4)
{
lean_object* v_declName_432_; uint8_t v___x_433_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; 
v_declName_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_declName_432_);
lean_dec_ref_known(v___x_431_, 2);
v___x_433_ = l_Lean_NameSet_contains(v_declNames_422_, v_declName_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_declName_432_);
lean_dec_ref(v_e_423_);
v___x_479_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_479_, 0, v___x_433_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v_env_482_; uint8_t v___x_483_; 
v___x_481_ = lean_st_ref_get(v_a_429_);
v_env_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref_n(v_env_482_, 2);
lean_dec(v___x_481_);
lean_inc(v_declName_432_);
v___x_483_ = l_Lean_Meta_hasSmartUnfoldingDecl(v_env_482_, v_declName_432_);
if (v___x_483_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Environment_find_x3f(v_env_482_, v_declName_432_, v___x_483_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_dec_ref(v_e_423_);
goto v___jp_484_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_489_; 
v_val_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = l_Lean_ConstantInfo_value_x3f(v_val_488_, v___x_483_);
if (lean_obj_tag(v___x_489_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_501_; 
v_val_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_501_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_501_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = l_Lean_Expr_getAppNumArgs(v_e_423_);
v___x_495_ = l_Lean_Expr_getNumHeadLambdas(v_val_490_);
lean_dec(v_val_490_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v___x_494_);
if (v___x_496_ == 0)
{
lean_del_object(v___x_492_);
v___y_435_ = v_a_424_;
v___y_436_ = v_a_425_;
v___y_437_ = v_a_426_;
v___y_438_ = v_a_427_;
v___y_439_ = v_a_428_;
v___y_440_ = v_a_429_;
goto v___jp_434_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec_ref(v_e_423_);
v___x_497_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_497_, 0, v___x_483_);
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 0);
lean_ctor_set(v___x_492_, 0, v___x_497_);
v___x_499_ = v___x_492_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec(v___x_489_);
lean_dec_ref(v_e_423_);
goto v___jp_484_;
}
}
}
else
{
lean_dec_ref(v_env_482_);
lean_dec(v_declName_432_);
v___y_435_ = v_a_424_;
v___y_436_ = v_a_425_;
v___y_437_ = v_a_426_;
v___y_438_ = v_a_427_;
v___y_439_ = v_a_428_;
v___y_440_ = v_a_429_;
goto v___jp_434_;
}
v___jp_484_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_485_, 0, v___x_483_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
v___jp_434_:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_423_, v___x_433_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_470_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_470_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_470_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_470_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
if (lean_obj_tag(v_a_442_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; 
lean_del_object(v___x_444_);
v_val_446_ = lean_ctor_get(v_a_442_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_a_442_, 1);
v___x_447_ = l_Lean_Meta_Sym_shareCommon(v_val_446_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_457_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = 0;
v___x_453_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_453_, 0, v_a_448_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v___x_452_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_447_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_447_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec(v_a_442_);
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0));
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_466_);
v___x_468_ = v___x_444_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_441_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_441_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref(v___x_431_);
lean_dec_ref(v_e_423_);
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_ofReduce_x3f___closed__0));
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_unfold___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_422_ = stack[0].m_obj;
lean_object* v_e_423_ = stack[1].m_obj;
lean_object* v_a_424_ = stack[2].m_obj;
lean_object* v_a_425_ = stack[3].m_obj;
lean_object* v_a_426_ = stack[4].m_obj;
lean_object* v_a_427_ = stack[5].m_obj;
lean_object* v_a_428_ = stack[6].m_obj;
lean_object* v_a_429_ = stack[7].m_obj;
lean_object* v_res_504_;
v_res_504_ = l_Lean_Meta_Sym_DSimp_unfold___redArg(v_declNames_422_, v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___redArg___boxed(lean_object* v_declNames_505_, lean_object* v_e_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Meta_Sym_DSimp_unfold___redArg(v_declNames_505_, v_e_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_declNames_505_);
return v_res_514_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_unfold(lean_object* v_declNames_515_, lean_object* v_e_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Meta_Sym_DSimp_unfold___redArg(v_declNames_515_, v_e_516_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_527_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_unfold_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_515_ = stack[0].m_obj;
lean_object* v_e_516_ = stack[1].m_obj;
lean_object* v_a_517_ = stack[2].m_obj;
lean_object* v_a_518_ = stack[3].m_obj;
lean_object* v_a_519_ = stack[4].m_obj;
lean_object* v_a_520_ = stack[5].m_obj;
lean_object* v_a_521_ = stack[6].m_obj;
lean_object* v_a_522_ = stack[7].m_obj;
lean_object* v_a_523_ = stack[8].m_obj;
lean_object* v_a_524_ = stack[9].m_obj;
lean_object* v_a_525_ = stack[10].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lean_Meta_Sym_DSimp_unfold(v_declNames_515_, v_e_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_unfold___boxed(lean_object* v_declNames_529_, lean_object* v_e_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_Sym_DSimp_unfold(v_declNames_529_, v_e_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec(v_declNames_529_);
return v_res_541_;
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
