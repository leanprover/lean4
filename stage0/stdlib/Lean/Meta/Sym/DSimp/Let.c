// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Let
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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v_b_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
lean_inc(v___y_2_);
v___x_13_ = lean_apply_11(v_k_1_, v_b_7_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v_b_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0(v_k_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v_b_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(lean_object* v_name_27_, lean_object* v_type_28_, lean_object* v_val_29_, lean_object* v_k_30_, uint8_t v_nondep_31_, uint8_t v_kind_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_43_, 0, v_k_30_);
lean_closure_set(v___f_43_, 1, v___y_33_);
lean_closure_set(v___f_43_, 2, v___y_34_);
lean_closure_set(v___f_43_, 3, v___y_35_);
lean_closure_set(v___f_43_, 4, v___y_36_);
lean_closure_set(v___f_43_, 5, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_27_, v_type_28_, v_val_29_, v___f_43_, v_nondep_31_, v_kind_32_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___boxed(lean_object* v_name_53_, lean_object* v_type_54_, lean_object* v_val_55_, lean_object* v_k_56_, lean_object* v_nondep_57_, lean_object* v_kind_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
uint8_t v_nondep_boxed_69_; uint8_t v_kind_boxed_70_; lean_object* v_res_71_; 
v_nondep_boxed_69_ = lean_unbox(v_nondep_57_);
v_kind_boxed_70_ = lean_unbox(v_kind_58_);
v_res_71_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_53_, v_type_54_, v_val_55_, v_k_56_, v_nondep_boxed_69_, v_kind_boxed_70_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(lean_object* v_fvarId_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = l_Lean_Expr_fvar___override(v_fvarId_72_);
v___x_76_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_75_, v___y_73_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v_fvarId_77_, v___y_78_);
lean_dec(v___y_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(lean_object* v_k_81_, lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = l_Lean_Expr_fvarId_x21(v_x_82_);
v___x_94_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v___x_93_, v___y_87_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_94_, 1);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
lean_inc(v___y_83_);
v___x_96_ = lean_apply_11(v_k_81_, v_a_95_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, lean_box(0));
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_k_81_);
v_a_97_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_94_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_105_, lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_105_, v_x_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v_x_106_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(lean_object* v_name_118_, lean_object* v_type_119_, lean_object* v_val_120_, lean_object* v_k_121_, uint8_t v_nondep_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___f_133_; uint8_t v___x_134_; lean_object* v___x_135_; 
v___f_133_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_133_, 0, v_k_121_);
v___x_134_ = 0;
v___x_135_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_118_, v_type_119_, v_val_120_, v___f_133_, v_nondep_122_, v___x_134_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___boxed(lean_object* v_name_136_, lean_object* v_type_137_, lean_object* v_val_138_, lean_object* v_k_139_, lean_object* v_nondep_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v_nondep_boxed_151_; lean_object* v_res_152_; 
v_nondep_boxed_151_ = lean_unbox(v_nondep_140_);
v_res_152_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_136_, v_type_137_, v_val_138_, v_k_139_, v_nondep_boxed_151_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(lean_object* v_fvars_153_, lean_object* v_body_154_, lean_object* v_modified_155_, lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v_modified_boxed_167_; lean_object* v_res_168_; 
v_modified_boxed_167_ = lean_unbox(v_modified_155_);
v_res_168_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(v_fvars_153_, v_body_154_, v_modified_boxed_167_, v_x_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(lean_object* v_fvars_169_, lean_object* v_body_170_, lean_object* v_x_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_array_push(v_fvars_169_, v_x_171_);
v___x_183_ = 1;
v___x_184_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_body_170_, v___x_182_, v___x_183_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed(lean_object* v_fvars_185_, lean_object* v_body_186_, lean_object* v_x_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(v_fvars_185_, v_body_186_, v_x_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(lean_object* v_e_199_, lean_object* v_fvars_200_, uint8_t v_modified_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
if (lean_obj_tag(v_e_199_) == 8)
{
lean_object* v_declName_212_; lean_object* v_type_213_; lean_object* v_value_214_; lean_object* v_body_215_; uint8_t v_nondep_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___x_220_; 
v_declName_212_ = lean_ctor_get(v_e_199_, 0);
lean_inc(v_declName_212_);
v_type_213_ = lean_ctor_get(v_e_199_, 1);
lean_inc_ref(v_type_213_);
v_value_214_ = lean_ctor_get(v_e_199_, 2);
lean_inc_ref(v_value_214_);
v_body_215_ = lean_ctor_get(v_e_199_, 3);
lean_inc_ref_n(v_body_215_, 2);
v_nondep_216_ = lean_ctor_get_uint8(v_e_199_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_199_, 4);
v___x_217_ = lean_box(v_modified_201_);
lean_inc_ref_n(v_fvars_200_, 3);
v___f_218_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed), 14, 3);
lean_closure_set(v___f_218_, 0, v_fvars_200_);
lean_closure_set(v___f_218_, 1, v_body_215_);
lean_closure_set(v___f_218_, 2, v___x_217_);
v___f_219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_219_, 0, v_fvars_200_);
lean_closure_set(v___f_219_, 1, v_body_215_);
v___x_220_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_type_213_, v_fvars_200_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_value_214_, v_fvars_200_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc(v_a_221_);
v___x_224_ = lean_sym_dsimp(v_a_221_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc(v_a_223_);
v___x_226_ = lean_sym_dsimp(v_a_223_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_226_) == 0)
{
if (lean_obj_tag(v_a_225_) == 0)
{
lean_object* v_a_227_; 
lean_dec_ref_known(v_a_225_, 0);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
if (lean_obj_tag(v_a_227_) == 0)
{
lean_object* v___x_228_; 
lean_dec_ref_known(v_a_227_, 0);
lean_dec_ref(v___f_219_);
v___x_228_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_212_, v_a_221_, v_a_223_, v___f_218_, v_nondep_216_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_228_;
}
else
{
lean_object* v_e_x27_229_; lean_object* v___x_230_; 
lean_dec(v_a_223_);
lean_dec_ref(v___f_218_);
v_e_x27_229_ = lean_ctor_get(v_a_227_, 0);
lean_inc_ref(v_e_x27_229_);
lean_dec_ref_known(v_a_227_, 1);
v___x_230_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_212_, v_a_221_, v_e_x27_229_, v___f_219_, v_nondep_216_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_230_;
}
}
else
{
lean_object* v_a_231_; 
lean_dec(v_a_221_);
lean_dec_ref(v___f_218_);
v_a_231_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_226_, 1);
if (lean_obj_tag(v_a_231_) == 0)
{
lean_object* v_e_x27_232_; lean_object* v___x_233_; 
lean_dec_ref_known(v_a_231_, 0);
v_e_x27_232_ = lean_ctor_get(v_a_225_, 0);
lean_inc_ref(v_e_x27_232_);
lean_dec_ref_known(v_a_225_, 1);
v___x_233_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_212_, v_e_x27_232_, v_a_223_, v___f_219_, v_nondep_216_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_233_;
}
else
{
lean_object* v_e_x27_234_; lean_object* v_e_x27_235_; lean_object* v___x_236_; 
lean_dec(v_a_223_);
v_e_x27_234_ = lean_ctor_get(v_a_225_, 0);
lean_inc_ref(v_e_x27_234_);
lean_dec_ref_known(v_a_225_, 1);
v_e_x27_235_ = lean_ctor_get(v_a_231_, 0);
lean_inc_ref(v_e_x27_235_);
lean_dec_ref_known(v_a_231_, 1);
v___x_236_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_212_, v_e_x27_234_, v_e_x27_235_, v___f_219_, v_nondep_216_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_236_;
}
}
}
else
{
lean_dec(v_a_225_);
lean_dec(v_a_223_);
lean_dec(v_a_221_);
lean_dec_ref(v___f_219_);
lean_dec_ref(v___f_218_);
lean_dec(v_declName_212_);
return v___x_226_;
}
}
else
{
lean_dec(v_a_223_);
lean_dec(v_a_221_);
lean_dec_ref(v___f_219_);
lean_dec_ref(v___f_218_);
lean_dec(v_declName_212_);
return v___x_224_;
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_a_221_);
lean_dec_ref(v___f_219_);
lean_dec_ref(v___f_218_);
lean_dec(v_declName_212_);
v_a_237_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_222_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_222_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v___f_219_);
lean_dec_ref(v___f_218_);
lean_dec_ref(v_value_214_);
lean_dec(v_declName_212_);
lean_dec_ref(v_fvars_200_);
v_a_245_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_220_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_220_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v___x_253_; 
lean_inc_ref(v_fvars_200_);
lean_inc_ref(v_e_199_);
v___x_253_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_199_, v_fvars_200_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
v___x_255_ = lean_sym_dsimp(v_a_254_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_317_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_317_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_317_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_317_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
if (lean_obj_tag(v_a_256_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_289_; 
v_isSharedCheck_289_ = !lean_is_exclusive(v_a_256_);
if (v_isSharedCheck_289_ == 0)
{
v___x_261_ = v_a_256_;
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_a_256_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_289_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
if (v_modified_201_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v_fvars_200_);
lean_dec_ref(v_e_199_);
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 0, 1);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
lean_ctor_set_uint8(v___x_264_, 0, v_modified_201_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_264_);
v___x_266_ = v___x_258_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
uint8_t v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; 
lean_del_object(v___x_261_);
lean_del_object(v___x_258_);
v___x_269_ = 0;
v___x_270_ = 1;
v___x_271_ = l_Lean_Meta_mkLetFVars(v_fvars_200_, v_e_199_, v___x_269_, v___x_269_, v___x_270_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec_ref(v_fvars_200_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_280_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_280_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_276_, 0, v_a_272_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_269_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_271_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
else
{
lean_object* v_e_x27_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_316_; 
lean_del_object(v___x_258_);
lean_dec_ref(v_e_199_);
v_e_x27_290_ = lean_ctor_get(v_a_256_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_256_);
if (v_isSharedCheck_316_ == 0)
{
v___x_292_ = v_a_256_;
v_isShared_293_ = v_isSharedCheck_316_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_e_x27_290_);
lean_dec(v_a_256_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_316_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v___x_294_ = 0;
v___x_295_ = 1;
v___x_296_ = l_Lean_Meta_mkLetFVars(v_fvars_200_, v_e_x27_290_, v___x_294_, v___x_294_, v___x_295_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec_ref(v_fvars_200_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v_a_297_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; 
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_294_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_292_);
v_a_308_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_296_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_296_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_fvars_200_);
lean_dec_ref(v_e_199_);
return v___x_255_;
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v_fvars_200_);
lean_dec_ref(v_e_199_);
v_a_318_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_253_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_253_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(lean_object* v_fvars_326_, lean_object* v_body_327_, uint8_t v_modified_328_, lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_array_push(v_fvars_326_, v_x_329_);
v___x_341_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_body_327_, v___x_340_, v_modified_328_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___boxed(lean_object* v_e_342_, lean_object* v_fvars_343_, lean_object* v_modified_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
uint8_t v_modified_boxed_355_; lean_object* v_res_356_; 
v_modified_boxed_355_ = lean_unbox(v_modified_344_);
v_res_356_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_342_, v_fvars_343_, v_modified_boxed_355_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0(lean_object* v_fvarId_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v_fvarId_357_, v___y_359_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___boxed(lean_object* v_fvarId_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0(v_fvarId_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1(lean_object* v_00_u03b1_375_, lean_object* v_name_376_, lean_object* v_type_377_, lean_object* v_val_378_, lean_object* v_k_379_, uint8_t v_nondep_380_, uint8_t v_kind_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_376_, v_type_377_, v_val_378_, v_k_379_, v_nondep_380_, v_kind_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_393_ = _args[0];
lean_object* v_name_394_ = _args[1];
lean_object* v_type_395_ = _args[2];
lean_object* v_val_396_ = _args[3];
lean_object* v_k_397_ = _args[4];
lean_object* v_nondep_398_ = _args[5];
lean_object* v_kind_399_ = _args[6];
lean_object* v___y_400_ = _args[7];
lean_object* v___y_401_ = _args[8];
lean_object* v___y_402_ = _args[9];
lean_object* v___y_403_ = _args[10];
lean_object* v___y_404_ = _args[11];
lean_object* v___y_405_ = _args[12];
lean_object* v___y_406_ = _args[13];
lean_object* v___y_407_ = _args[14];
lean_object* v___y_408_ = _args[15];
lean_object* v___y_409_ = _args[16];
_start:
{
uint8_t v_nondep_boxed_410_; uint8_t v_kind_boxed_411_; lean_object* v_res_412_; 
v_nondep_boxed_410_ = lean_unbox(v_nondep_398_);
v_kind_boxed_411_ = lean_unbox(v_kind_399_);
v_res_412_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1(v_00_u03b1_393_, v_name_394_, v_type_395_, v_val_396_, v_k_397_, v_nondep_boxed_410_, v_kind_boxed_411_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(lean_object* v_00_u03b1_413_, lean_object* v_name_414_, lean_object* v_type_415_, lean_object* v_val_416_, lean_object* v_k_417_, uint8_t v_nondep_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_414_, v_type_415_, v_val_416_, v_k_417_, v_nondep_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_name_431_, lean_object* v_type_432_, lean_object* v_val_433_, lean_object* v_k_434_, lean_object* v_nondep_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v_nondep_boxed_446_; lean_object* v_res_447_; 
v_nondep_boxed_446_ = lean_unbox(v_nondep_435_);
v_res_447_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(v_00_u03b1_430_, v_name_431_, v_type_432_, v_val_433_, v_k_434_, v_nondep_boxed_446_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object* v_e_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; 
v___x_461_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0));
v___x_462_ = 0;
v___x_463_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_450_, v___x_461_, v___x_462_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
return v_res_475_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin) {
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
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Let(builtin);
}
#ifdef __cplusplus
}
#endif
