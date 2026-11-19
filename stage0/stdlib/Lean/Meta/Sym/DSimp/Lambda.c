// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Lambda
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.Util
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg(lean_object* v_fvarId_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Expr_fvar___override(v_fvarId_1_);
v___x_5_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_4_, v___y_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg(v_fvarId_6_, v___y_7_);
lean_dec(v___y_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0(lean_object* v_k_10_, lean_object* v_x_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_Expr_fvarId_x21(v_x_11_);
v___x_23_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg(v___x_22_, v___y_16_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_25_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_23_, 1);
lean_inc(v___y_20_);
lean_inc_ref(v___y_19_);
lean_inc(v___y_18_);
lean_inc_ref(v___y_17_);
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc(v___y_12_);
v___x_25_ = lean_apply_11(v_k_10_, v_a_24_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, lean_box(0));
return v___x_25_;
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec_ref(v_k_10_);
v_a_26_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_23_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_23_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0(v_k_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v_x_35_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___lam__0(lean_object* v_k_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v_b_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
lean_inc(v___y_48_);
v___x_59_ = lean_apply_11(v_k_47_, v_b_53_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, lean_box(0));
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v_b_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___lam__0(v_k_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v_b_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg(lean_object* v_name_73_, uint8_t v_bi_74_, lean_object* v_type_75_, lean_object* v_k_76_, uint8_t v_kind_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; 
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc(v___y_80_);
lean_inc_ref(v___y_79_);
lean_inc(v___y_78_);
v___f_88_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_88_, 0, v_k_76_);
lean_closure_set(v___f_88_, 1, v___y_78_);
lean_closure_set(v___f_88_, 2, v___y_79_);
lean_closure_set(v___f_88_, 3, v___y_80_);
lean_closure_set(v___f_88_, 4, v___y_81_);
lean_closure_set(v___f_88_, 5, v___y_82_);
v___x_89_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_73_, v_bi_74_, v_type_75_, v___f_88_, v_kind_77_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
if (lean_obj_tag(v___x_89_) == 0)
{
return v___x_89_;
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg___boxed(lean_object* v_name_98_, lean_object* v_bi_99_, lean_object* v_type_100_, lean_object* v_k_101_, lean_object* v_kind_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
uint8_t v_bi_boxed_113_; uint8_t v_kind_boxed_114_; lean_object* v_res_115_; 
v_bi_boxed_113_ = lean_unbox(v_bi_99_);
v_kind_boxed_114_ = lean_unbox(v_kind_102_);
v_res_115_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg(v_name_98_, v_bi_boxed_113_, v_type_100_, v_k_101_, v_kind_boxed_114_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(lean_object* v_name_116_, uint8_t v_bi_117_, lean_object* v_type_118_, lean_object* v_k_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___f_130_; uint8_t v___x_131_; lean_object* v___x_132_; 
v___f_130_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_130_, 0, v_k_119_);
v___x_131_ = 0;
v___x_132_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg(v_name_116_, v_bi_117_, v_type_118_, v___f_130_, v___x_131_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___boxed(lean_object* v_name_133_, lean_object* v_bi_134_, lean_object* v_type_135_, lean_object* v_k_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
uint8_t v_bi_boxed_147_; lean_object* v_res_148_; 
v_bi_boxed_147_ = lean_unbox(v_bi_134_);
v_res_148_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_name_133_, v_bi_boxed_147_, v_type_135_, v_k_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0___boxed(lean_object* v_fvars_149_, lean_object* v_body_150_, lean_object* v_modified_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v_modified_boxed_163_; lean_object* v_res_164_; 
v_modified_boxed_163_ = lean_unbox(v_modified_151_);
v_res_164_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0(v_fvars_149_, v_body_150_, v_modified_boxed_163_, v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1(lean_object* v_fvars_165_, lean_object* v_body_166_, lean_object* v_x_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_array_push(v_fvars_165_, v_x_167_);
v___x_179_ = 1;
v___x_180_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_body_166_, v___x_178_, v___x_179_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1___boxed(lean_object* v_fvars_181_, lean_object* v_body_182_, lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1(v_fvars_181_, v_body_182_, v_x_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(lean_object* v_e_195_, lean_object* v_fvars_196_, uint8_t v_modified_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
if (lean_obj_tag(v_e_195_) == 6)
{
lean_object* v_binderName_208_; lean_object* v_binderType_209_; lean_object* v_body_210_; uint8_t v_binderInfo_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___x_215_; 
v_binderName_208_ = lean_ctor_get(v_e_195_, 0);
lean_inc(v_binderName_208_);
v_binderType_209_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_binderType_209_);
v_body_210_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref_n(v_body_210_, 2);
v_binderInfo_211_ = lean_ctor_get_uint8(v_e_195_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_195_, 3);
v___x_212_ = lean_box(v_modified_197_);
lean_inc_ref_n(v_fvars_196_, 2);
v___f_213_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0___boxed), 14, 3);
lean_closure_set(v___f_213_, 0, v_fvars_196_);
lean_closure_set(v___f_213_, 1, v_body_210_);
lean_closure_set(v___f_213_, 2, v___x_212_);
v___f_214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_214_, 0, v_fvars_196_);
lean_closure_set(v___f_214_, 1, v_body_210_);
v___x_215_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_binderType_209_, v_fvars_196_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc_n(v_a_216_, 2);
lean_dec_ref_known(v___x_215_, 1);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
lean_inc(v_a_200_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_198_);
v___x_217_ = lean_sym_dsimp(v_a_216_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
if (lean_obj_tag(v_a_218_) == 0)
{
lean_object* v___x_219_; 
lean_dec_ref_known(v_a_218_, 0);
lean_dec_ref(v___f_214_);
v___x_219_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_binderName_208_, v_binderInfo_211_, v_a_216_, v___f_213_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_219_;
}
else
{
lean_object* v_e_x27_220_; lean_object* v___x_221_; 
lean_dec(v_a_216_);
lean_dec_ref(v___f_213_);
v_e_x27_220_ = lean_ctor_get(v_a_218_, 0);
lean_inc_ref(v_e_x27_220_);
lean_dec_ref_known(v_a_218_, 1);
v___x_221_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_binderName_208_, v_binderInfo_211_, v_e_x27_220_, v___f_214_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_221_;
}
}
else
{
lean_dec(v_a_216_);
lean_dec_ref(v___f_214_);
lean_dec_ref(v___f_213_);
lean_dec(v_binderName_208_);
return v___x_217_;
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___f_214_);
lean_dec_ref(v___f_213_);
lean_dec(v_binderName_208_);
v_a_222_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_215_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_215_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v___x_230_; 
lean_inc_ref(v_fvars_196_);
lean_inc_ref(v_e_195_);
v___x_230_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_195_, v_fvars_196_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
lean_inc(v_a_200_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_198_);
v___x_232_ = lean_sym_dsimp(v_a_231_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_292_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_292_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_292_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_292_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
if (lean_obj_tag(v_a_233_) == 0)
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_265_; 
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_265_ == 0)
{
v___x_238_ = v_a_233_;
v_isShared_239_ = v_isSharedCheck_265_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_a_233_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_265_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
if (v_modified_197_ == 0)
{
lean_object* v___x_241_; 
lean_dec_ref(v_fvars_196_);
lean_dec_ref(v_e_195_);
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 0, 1);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
lean_ctor_set_uint8(v___x_241_, 0, v_modified_197_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_241_);
v___x_243_ = v___x_235_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v___x_246_; 
lean_del_object(v___x_238_);
lean_del_object(v___x_235_);
v___x_246_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_fvars_196_, v_e_195_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_256_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_256_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_256_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_256_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_251_ = 0;
v___x_252_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_252_, 0, v_a_247_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v___x_251_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_252_);
v___x_254_ = v___x_249_;
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
v_a_257_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_246_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_246_);
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
}
else
{
lean_object* v_e_x27_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_291_; 
lean_del_object(v___x_235_);
lean_dec_ref(v_e_195_);
v_e_x27_266_ = lean_ctor_get(v_a_233_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_291_ == 0)
{
v___x_268_ = v_a_233_;
v_isShared_269_ = v_isSharedCheck_291_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_e_x27_266_);
lean_dec(v_a_233_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_291_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_fvars_196_, v_e_x27_266_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_282_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_282_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; lean_object* v___x_277_; 
v___x_275_ = 0;
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_a_271_);
v___x_277_ = v___x_268_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_271_);
v___x_277_ = v_reuseFailAlloc_281_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_279_; 
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_275_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_277_);
v___x_279_ = v___x_273_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_del_object(v___x_268_);
v_a_283_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_270_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_270_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_fvars_196_);
lean_dec_ref(v_e_195_);
return v___x_232_;
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_fvars_196_);
lean_dec_ref(v_e_195_);
v_a_293_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_230_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_230_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0(lean_object* v_fvars_301_, lean_object* v_body_302_, uint8_t v_modified_303_, lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_array_push(v_fvars_301_, v_x_304_);
v___x_316_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_body_302_, v___x_315_, v_modified_303_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___boxed(lean_object* v_e_317_, lean_object* v_fvars_318_, lean_object* v_modified_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
uint8_t v_modified_boxed_330_; lean_object* v_res_331_; 
v_modified_boxed_330_ = lean_unbox(v_modified_319_);
v_res_331_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_e_317_, v_fvars_318_, v_modified_boxed_330_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0(lean_object* v_fvarId_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___redArg(v_fvarId_332_, v___y_334_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0___boxed(lean_object* v_fvarId_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__0(v_fvarId_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1(lean_object* v_00_u03b1_350_, lean_object* v_name_351_, uint8_t v_bi_352_, lean_object* v_type_353_, lean_object* v_k_354_, uint8_t v_kind_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___redArg(v_name_351_, v_bi_352_, v_type_353_, v_k_354_, v_kind_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_367_, lean_object* v_name_368_, lean_object* v_bi_369_, lean_object* v_type_370_, lean_object* v_k_371_, lean_object* v_kind_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
uint8_t v_bi_boxed_383_; uint8_t v_kind_boxed_384_; lean_object* v_res_385_; 
v_bi_boxed_383_ = lean_unbox(v_bi_369_);
v_kind_boxed_384_ = lean_unbox(v_kind_372_);
v_res_385_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0_spec__1(v_00_u03b1_367_, v_name_368_, v_bi_boxed_383_, v_type_370_, v_k_371_, v_kind_boxed_384_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0(lean_object* v_00_u03b1_386_, lean_object* v_name_387_, uint8_t v_bi_388_, lean_object* v_type_389_, lean_object* v_k_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_name_387_, v_bi_388_, v_type_389_, v_k_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___boxed(lean_object* v_00_u03b1_402_, lean_object* v_name_403_, lean_object* v_bi_404_, lean_object* v_type_405_, lean_object* v_k_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v_bi_boxed_417_; lean_object* v_res_418_; 
v_bi_boxed_417_ = lean_unbox(v_bi_404_);
v_res_418_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0(v_00_u03b1_402_, v_name_403_, v_bi_boxed_417_, v_type_405_, v_k_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda(lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0));
v___x_433_ = 0;
v___x_434_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_e_421_, v___x_432_, v___x_433_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda___boxed(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
return v_res_446_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
}
#ifdef __cplusplus
}
#endif
