// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Reduce
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.Util import Lean.Meta.WHNF import Lean.ProjFns
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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object* v_e_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = l_Lean_Expr_isApp(v_e_3_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v_e_3_);
v___x_12_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_12_, 0, v___x_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v_f_14_; uint8_t v___x_15_; uint8_t v___x_16_; 
v_f_14_ = l_Lean_Expr_getAppFn(v_e_3_);
v___x_15_ = 0;
v___x_16_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_15_, v_f_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec_ref(v_f_14_);
lean_dec_ref(v_e_3_);
v___x_17_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_19_ = l_Lean_Expr_getAppNumArgs(v_e_3_);
v___x_20_ = lean_mk_empty_array_with_capacity(v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3_, v___x_20_);
v___x_22_ = l_Lean_Meta_Sym_betaRevS(v_f_14_, v___x_21_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_31_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_31_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_27_, 0, v_a_23_);
lean_ctor_set_uint8(v___x_27_, sizeof(void*)*1, v___x_15_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_27_);
v___x_29_ = v___x_25_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_22_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_22_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object* v_e_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_49_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object* v_e_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_Sym_DSimp_beta(v_e_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec(v_a_63_);
lean_dec(v_a_62_);
return v_res_72_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(lean_object* v_k_73_, lean_object* v_t_74_){
_start:
{
if (lean_obj_tag(v_t_74_) == 0)
{
lean_object* v_k_75_; lean_object* v_l_76_; lean_object* v_r_77_; uint8_t v___x_78_; 
v_k_75_ = lean_ctor_get(v_t_74_, 1);
v_l_76_ = lean_ctor_get(v_t_74_, 3);
v_r_77_ = lean_ctor_get(v_t_74_, 4);
v___x_78_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_73_, v_k_75_);
switch(v___x_78_)
{
case 0:
{
v_t_74_ = v_l_76_;
goto _start;
}
case 1:
{
uint8_t v___x_80_; 
v___x_80_ = 1;
return v___x_80_;
}
default: 
{
v_t_74_ = v_r_77_;
goto _start;
}
}
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg___boxed(lean_object* v_k_83_, lean_object* v_t_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_83_, v_t_84_);
lean_dec(v_t_84_);
lean_dec(v_k_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(lean_object* v_s_87_, lean_object* v_e_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
if (lean_obj_tag(v_e_88_) == 1)
{
lean_object* v_fvarId_93_; uint8_t v___x_94_; 
v_fvarId_93_ = lean_ctor_get(v_e_88_, 0);
lean_inc(v_fvarId_93_);
lean_dec_ref_known(v_e_88_, 1);
v___x_94_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_fvarId_93_, v_s_87_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_fvarId_93_);
v___x_95_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_93_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_113_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_113_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_113_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_113_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
uint8_t v___x_102_; lean_object* v___x_103_; 
v___x_102_ = 0;
v___x_103_ = l_Lean_LocalDecl_value_x3f(v_a_98_, v___x_102_);
lean_dec(v_a_98_);
if (lean_obj_tag(v___x_103_) == 1)
{
lean_object* v_val_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v_val_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_105_, 0, v_val_104_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_102_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_105_);
v___x_107_ = v___x_100_;
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
else
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec(v___x_103_);
v___x_109_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_109_);
v___x_111_ = v___x_100_;
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
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_97_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_97_);
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
else
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec_ref(v_e_88_);
v___x_122_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___boxed(lean_object* v_s_124_, lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_124_, v_e_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_s_124_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta(lean_object* v_s_131_, lean_object* v_e_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_131_, v_e_132_, v_a_138_, v_a_140_, v_a_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDelta___boxed(lean_object* v_s_144_, lean_object* v_e_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_Sym_DSimp_zetaDelta(v_s_144_, v_e_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec(v_a_147_);
lean_dec(v_a_146_);
lean_dec(v_s_144_);
return v_res_156_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(lean_object* v_00_u03b2_157_, lean_object* v_k_158_, lean_object* v_t_159_){
_start:
{
uint8_t v___x_160_; 
v___x_160_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_158_, v_t_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___boxed(lean_object* v_00_u03b2_161_, lean_object* v_k_162_, lean_object* v_t_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(v_00_u03b2_161_, v_k_162_, v_t_163_);
lean_dec(v_t_163_);
lean_dec(v_k_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object* v_e_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
if (lean_obj_tag(v_e_166_) == 1)
{
lean_object* v_fvarId_171_; lean_object* v___x_172_; 
v_fvarId_171_ = lean_ctor_get(v_e_166_, 0);
lean_inc(v_fvarId_171_);
lean_dec_ref_known(v_e_166_, 1);
v___x_172_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_171_, v_a_167_, v_a_168_, v_a_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_188_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_188_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_188_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint8_t v___x_177_; lean_object* v___x_178_; 
v___x_177_ = 0;
v___x_178_ = l_Lean_LocalDecl_value_x3f(v_a_173_, v___x_177_);
lean_dec(v_a_173_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_180_, 0, v_val_179_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*1, v___x_177_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_180_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v___x_178_);
v___x_184_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_184_);
v___x_186_ = v___x_175_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_172_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_172_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v_e_166_);
v___x_197_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___boxed(lean_object* v_e_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll(lean_object* v_e_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_205_, v_a_211_, v_a_213_, v_a_214_);
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
lean_dec(v_a_219_);
lean_dec(v_a_218_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(lean_object* v_e_229_, lean_object* v_subst_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
if (lean_obj_tag(v_e_229_) == 8)
{
lean_object* v_value_238_; lean_object* v_body_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_value_238_ = lean_ctor_get(v_e_229_, 2);
lean_inc_ref(v_value_238_);
v_body_239_ = lean_ctor_get(v_e_229_, 3);
lean_inc_ref(v_body_239_);
lean_dec_ref_known(v_e_229_, 4);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_array_get_size(v_subst_230_);
lean_inc_ref(v_subst_230_);
v___x_242_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_238_, v___x_240_, v___x_241_, v_subst_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = lean_array_push(v_subst_230_, v_a_243_);
v_e_229_ = v_body_239_;
v_subst_230_ = v___x_244_;
goto _start;
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_body_239_);
lean_dec_ref(v_subst_230_);
v_a_246_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_242_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_242_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_array_get_size(v_subst_230_);
v___x_256_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_229_, v___x_254_, v___x_255_, v_subst_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_266_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_266_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = 0;
v___x_262_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_262_, 0, v_a_257_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_261_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_256_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_256_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg___boxed(lean_object* v_e_275_, lean_object* v_subst_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(v_e_275_, v_subst_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go(lean_object* v_e_285_, lean_object* v_subst_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(v_e_285_, v_subst_286_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___boxed(lean_object* v_e_298_, lean_object* v_subst_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go(v_e_298_, v_subst_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_a_300_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object* v_e_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
if (lean_obj_tag(v_e_313_) == 8)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0));
v___x_322_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(v_e_313_, v___x_321_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v_e_313_);
v___x_323_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object* v_e_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_334_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object* v_e_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Sym_DSimp_zeta(v_e_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(lean_object* v_declName_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_env_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_st_ref_get(v___y_359_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v___x_363_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_362_, v_declName_358_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg___boxed(lean_object* v_declName_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_365_, v___y_366_);
lean_dec(v___y_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(lean_object* v_declName_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_369_, v___y_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___boxed(lean_object* v_declName_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(v_declName_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
lean_dec(v___y_382_);
return v_res_392_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0(void){
_start:
{
lean_object* v___x_393_; lean_object* v_dummy_394_; 
v___x_393_ = lean_box(0);
v_dummy_394_ = l_Lean_Expr_sort___override(v___x_393_);
return v_dummy_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object* v_e_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_f_409_; 
v_f_409_ = l_Lean_Expr_getAppFn(v_e_395_);
if (lean_obj_tag(v_f_409_) == 4)
{
lean_object* v_declName_410_; lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_469_; 
v_declName_410_ = lean_ctor_get(v_f_409_, 0);
lean_inc(v_declName_410_);
lean_dec_ref_known(v_f_409_, 2);
v___x_411_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_410_, v_a_404_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_469_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_469_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_469_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
if (lean_obj_tag(v_a_412_) == 1)
{
uint8_t v___x_416_; lean_object* v___x_417_; 
lean_dec_ref_known(v_a_412_, 1);
lean_del_object(v___x_414_);
v___x_416_ = 0;
v___x_417_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_395_, v___x_416_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
if (lean_obj_tag(v_a_418_) == 0)
{
goto v___jp_406_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_val_419_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_a_418_, 1);
v___x_420_ = l_Lean_Expr_getAppFn(v_val_419_);
v___x_421_ = l_Lean_Meta_reduceProj_x3f(v___x_420_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
if (lean_obj_tag(v_a_422_) == 0)
{
lean_dec(v_val_419_);
goto v___jp_406_;
}
else
{
lean_object* v_val_423_; lean_object* v_dummy_424_; lean_object* v_nargs_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_val_423_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref_known(v_a_422_, 1);
v_dummy_424_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0, &l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0);
v_nargs_425_ = l_Lean_Expr_getAppNumArgs(v_val_419_);
lean_inc(v_nargs_425_);
v___x_426_ = lean_mk_array(v_nargs_425_, v_dummy_424_);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_sub(v_nargs_425_, v___x_427_);
lean_dec(v_nargs_425_);
v___x_429_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_419_, v___x_426_, v___x_428_);
v___x_430_ = l_Lean_mkAppN(v_val_423_, v___x_429_);
lean_dec_ref(v___x_429_);
v___x_431_ = l_Lean_Meta_Sym_shareCommon(v___x_430_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_436_, 0, v_a_432_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_416_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_431_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_val_419_);
v_a_449_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_421_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_421_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_417_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_417_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_467_; 
lean_dec(v_a_412_);
lean_dec_ref(v_e_395_);
v___x_465_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_465_);
v___x_467_ = v___x_414_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec_ref(v_f_409_);
lean_dec_ref(v_e_395_);
v___x_470_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
v___jp_406_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object* v_e_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v_e_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec(v_a_474_);
lean_dec(v_a_473_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object* v_e_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_484_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_531_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_531_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_531_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_531_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_del_object(v___x_495_);
v_val_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_a_493_, 1);
v___x_498_ = l_Lean_Meta_Sym_foldProjs(v_val_497_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = l_Lean_Meta_Sym_shareCommonInc(v_a_499_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_510_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = 0;
v___x_506_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_506_, 0, v_a_501_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*1, v___x_505_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_506_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_500_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_500_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_498_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_a_493_);
v___x_527_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_527_);
v___x_529_ = v___x_495_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_492_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_492_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object* v_e_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec_ref(v_e_540_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_549_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_Sym_DSimp_dsimpMatch(v_e_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_e_561_);
return v_res_572_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
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
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
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
