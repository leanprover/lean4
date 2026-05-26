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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_Lean_Expr_isApp(v_e_3_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec_ref(v_e_3_);
v___x_7_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_7_, 0, v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v_f_9_; uint8_t v___x_10_; uint8_t v___x_11_; 
v_f_9_ = l_Lean_Expr_getAppFn(v_e_3_);
v___x_10_ = 0;
v___x_11_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_10_, v_f_9_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v_f_9_);
lean_dec_ref(v_e_3_);
v___x_12_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_14_ = l_Lean_Expr_getAppNumArgs(v_e_3_);
v___x_15_ = lean_mk_empty_array_with_capacity(v___x_14_);
lean_dec(v___x_14_);
v___x_16_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3_, v___x_15_);
v___x_17_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_9_, v___x_16_, v_a_4_);
lean_dec_ref(v___x_16_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_26_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_26_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_22_, 0, v_a_18_);
lean_ctor_set_uint8(v___x_22_, sizeof(void*)*1, v___x_10_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_22_);
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
v_a_27_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_17_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_17_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_35_, v_a_36_);
lean_dec(v_a_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta(lean_object* v_e_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_39_, v_a_44_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_beta___boxed(lean_object* v_e_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Sym_DSimp_beta(v_e_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec(v_a_53_);
lean_dec(v_a_52_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg(lean_object* v_k_63_, lean_object* v_t_64_){
_start:
{
if (lean_obj_tag(v_t_64_) == 0)
{
lean_object* v_k_65_; lean_object* v_l_66_; lean_object* v_r_67_; uint8_t v___x_68_; 
v_k_65_ = lean_ctor_get(v_t_64_, 1);
v_l_66_ = lean_ctor_get(v_t_64_, 3);
v_r_67_ = lean_ctor_get(v_t_64_, 4);
v___x_68_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_63_, v_k_65_);
switch(v___x_68_)
{
case 0:
{
v_t_64_ = v_l_66_;
goto _start;
}
case 1:
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
default: 
{
v_t_64_ = v_r_67_;
goto _start;
}
}
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg___boxed(lean_object* v_k_73_, lean_object* v_t_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg(v_k_73_, v_t_74_);
lean_dec(v_t_74_);
lean_dec(v_k_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object* v_s_77_, lean_object* v_e_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
if (lean_obj_tag(v_e_78_) == 1)
{
lean_object* v_fvarId_83_; uint8_t v___x_84_; 
v_fvarId_83_ = lean_ctor_get(v_e_78_, 0);
lean_inc(v_fvarId_83_);
lean_dec_ref_known(v_e_78_, 1);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg(v_fvarId_83_, v_s_77_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_fvarId_83_);
v___x_85_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_85_, 0, v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_83_, v_a_79_, v_a_80_, v_a_81_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_103_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_103_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_103_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_103_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint8_t v___x_92_; lean_object* v___x_93_; 
v___x_92_ = 0;
v___x_93_ = l_Lean_LocalDecl_value_x3f(v_a_88_, v___x_92_);
lean_dec(v_a_88_);
if (lean_obj_tag(v___x_93_) == 1)
{
lean_object* v_val_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v_val_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_val_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_95_, 0, v_val_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_92_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_95_);
v___x_97_ = v___x_90_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_101_; 
lean_dec(v___x_93_);
v___x_99_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_99_);
v___x_101_ = v___x_90_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_87_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_87_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec_ref(v_e_78_);
v___x_112_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(lean_object* v_s_114_, lean_object* v_e_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_s_114_, v_e_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_s_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta(lean_object* v_s_121_, lean_object* v_e_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_s_121_, v_e_122_, v_a_128_, v_a_130_, v_a_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zeta___boxed(lean_object* v_s_134_, lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_Sym_DSimp_zeta(v_s_134_, v_e_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec(v_a_137_);
lean_dec(v_a_136_);
lean_dec(v_s_134_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0(lean_object* v_00_u03b2_147_, lean_object* v_k_148_, lean_object* v_t_149_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___redArg(v_k_148_, v_t_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0___boxed(lean_object* v_00_u03b2_151_, lean_object* v_k_152_, lean_object* v_t_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zeta_spec__0(v_00_u03b2_151_, v_k_152_, v_t_153_);
lean_dec(v_t_153_);
lean_dec(v_k_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll___redArg(lean_object* v_e_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
if (lean_obj_tag(v_e_156_) == 1)
{
lean_object* v_fvarId_161_; lean_object* v___x_162_; 
v_fvarId_161_ = lean_ctor_get(v_e_156_, 0);
lean_inc(v_fvarId_161_);
lean_dec_ref_known(v_e_156_, 1);
v___x_162_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_161_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_178_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_178_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_178_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_178_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_167_ = 0;
v___x_168_ = l_Lean_LocalDecl_value_x3f(v_a_163_, v___x_167_);
lean_dec(v_a_163_);
if (lean_obj_tag(v___x_168_) == 1)
{
lean_object* v_val_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v_val_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_168_, 1);
v___x_170_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_170_, 0, v_val_169_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*1, v___x_167_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_170_);
v___x_172_ = v___x_165_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_176_; 
lean_dec(v___x_168_);
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_174_);
v___x_176_ = v___x_165_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_162_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_162_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_e_156_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll___redArg___boxed(lean_object* v_e_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Meta_Sym_DSimp_zetaAll___redArg(v_e_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll(lean_object* v_e_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Sym_DSimp_zetaAll___redArg(v_e_195_, v_a_201_, v_a_203_, v_a_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_zetaAll___boxed(lean_object* v_e_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Meta_Sym_DSimp_zetaAll(v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
lean_dec(v_a_208_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(lean_object* v_declName_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_env_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_st_ref_get(v___y_220_);
v_env_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_env_223_);
lean_dec(v___x_222_);
v___x_224_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_223_, v_declName_219_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg___boxed(lean_object* v_declName_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_226_, v___y_227_);
lean_dec(v___y_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(lean_object* v_declName_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_230_, v___y_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___boxed(lean_object* v_declName_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(v_declName_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v___y_243_);
return v_res_253_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v_dummy_255_; 
v___x_254_ = lean_box(0);
v_dummy_255_ = l_Lean_Expr_sort___override(v___x_254_);
return v_dummy_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object* v_e_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_f_270_; 
v_f_270_ = l_Lean_Expr_getAppFn(v_e_256_);
if (lean_obj_tag(v_f_270_) == 4)
{
lean_object* v_declName_271_; lean_object* v___x_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_330_; 
v_declName_271_ = lean_ctor_get(v_f_270_, 0);
lean_inc(v_declName_271_);
lean_dec_ref_known(v_f_270_, 2);
v___x_272_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_271_, v_a_265_);
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_330_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_330_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_330_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
if (lean_obj_tag(v_a_273_) == 1)
{
uint8_t v___x_277_; lean_object* v___x_278_; 
lean_dec_ref_known(v_a_273_, 1);
lean_del_object(v___x_275_);
v___x_277_ = 0;
v___x_278_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_256_, v___x_277_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
if (lean_obj_tag(v_a_279_) == 0)
{
goto v___jp_267_;
}
else
{
lean_object* v_val_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_val_280_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_a_279_, 1);
v___x_281_ = l_Lean_Expr_getAppFn(v_val_280_);
v___x_282_ = l_Lean_Meta_reduceProj_x3f(v___x_281_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
if (lean_obj_tag(v_a_283_) == 0)
{
lean_dec(v_val_280_);
goto v___jp_267_;
}
else
{
lean_object* v_val_284_; lean_object* v_dummy_285_; lean_object* v_nargs_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_val_284_ = lean_ctor_get(v_a_283_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v_a_283_, 1);
v_dummy_285_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0, &l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0);
v_nargs_286_ = l_Lean_Expr_getAppNumArgs(v_val_280_);
lean_inc(v_nargs_286_);
v___x_287_ = lean_mk_array(v_nargs_286_, v_dummy_285_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_sub(v_nargs_286_, v___x_288_);
lean_dec(v_nargs_286_);
v___x_290_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_280_, v___x_287_, v___x_289_);
v___x_291_ = l_Lean_mkAppN(v_val_284_, v___x_290_);
lean_dec_ref(v___x_290_);
v___x_292_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_291_, v_a_261_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_297_, 0, v_a_293_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___x_277_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_292_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_292_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v_val_280_);
v_a_310_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_282_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_282_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
v_a_318_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_278_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_278_);
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
else
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec(v_a_273_);
lean_dec_ref(v_e_256_);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_326_);
v___x_328_ = v___x_275_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v_f_270_);
lean_dec_ref(v_e_256_);
v___x_331_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
v___jp_267_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(lean_object* v_e_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v_e_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec(v_a_335_);
lean_dec(v_a_334_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object* v_e_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_345_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_399_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_399_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_399_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_399_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
if (lean_obj_tag(v_a_353_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_358_; 
lean_del_object(v___x_355_);
v_val_357_ = lean_ctor_get(v_a_353_, 0);
lean_inc_n(v_val_357_, 2);
lean_dec_ref_known(v_a_353_, 1);
v___x_358_ = l_Lean_Meta_Sym_foldProjs(v_val_357_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_386_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_386_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_386_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_386_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
uint8_t v___x_363_; 
v___x_363_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_val_357_, v_a_359_);
lean_dec(v_val_357_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_del_object(v___x_361_);
v___x_364_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_359_, v_a_346_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_369_, 0, v_a_365_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*1, v___x_363_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec(v_a_359_);
v___x_382_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_382_);
v___x_384_ = v___x_361_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
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
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_val_357_);
v_a_387_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_358_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_358_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec(v_a_353_);
v___x_395_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0));
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_395_);
v___x_397_ = v___x_355_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_a_400_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_352_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_352_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_e_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch(lean_object* v_e_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_416_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Sym_DSimp_dsimpMatch(v_e_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_e_428_);
return v_res_439_;
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
