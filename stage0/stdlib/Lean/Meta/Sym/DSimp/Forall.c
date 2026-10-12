// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Forall
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg(lean_object* v_fvarId_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Expr_fvar___override(v_fvarId_1_);
v___x_5_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_4_, v___y_2_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_6_;
v_res_6_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg(v_fvarId_1_, v___y_2_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg(v_fvarId_7_, v___y_8_);
lean_dec(v___y_8_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0(lean_object* v_k_11_, lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = l_Lean_Expr_fvarId_x21(v_x_12_);
v___x_24_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg(v___x_23_, v___y_17_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_26_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_a_25_);
lean_dec_ref_known(v___x_24_, 1);
lean_inc(v___y_21_);
lean_inc_ref(v___y_20_);
lean_inc(v___y_19_);
lean_inc_ref(v___y_18_);
lean_inc(v___y_17_);
lean_inc_ref(v___y_16_);
lean_inc(v___y_15_);
lean_inc_ref(v___y_14_);
lean_inc(v___y_13_);
v___x_26_ = lean_apply_11(v_k_11_, v_a_25_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, lean_box(0));
return v___x_26_;
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
lean_dec_ref(v_k_11_);
v_a_27_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_24_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_24_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_11_ = stack[0].m_obj;
lean_object* v_x_12_ = stack[1].m_obj;
lean_object* v___y_13_ = stack[2].m_obj;
lean_object* v___y_14_ = stack[3].m_obj;
lean_object* v___y_15_ = stack[4].m_obj;
lean_object* v___y_16_ = stack[5].m_obj;
lean_object* v___y_17_ = stack[6].m_obj;
lean_object* v___y_18_ = stack[7].m_obj;
lean_object* v___y_19_ = stack[8].m_obj;
lean_object* v___y_20_ = stack[9].m_obj;
lean_object* v___y_21_ = stack[10].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0(v_k_11_, v_x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_36_, lean_object* v_x_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0(v_k_36_, v_x_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v_x_37_);
return v_res_48_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0(lean_object* v_k_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v_b_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___y_50_);
v___x_61_ = lean_apply_11(v_k_49_, v_b_55_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, lean_box(0));
return v___x_61_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_49_ = stack[0].m_obj;
lean_object* v___y_50_ = stack[1].m_obj;
lean_object* v___y_51_ = stack[2].m_obj;
lean_object* v___y_52_ = stack[3].m_obj;
lean_object* v___y_53_ = stack[4].m_obj;
lean_object* v___y_54_ = stack[5].m_obj;
lean_object* v_b_55_ = stack[6].m_obj;
lean_object* v___y_56_ = stack[7].m_obj;
lean_object* v___y_57_ = stack[8].m_obj;
lean_object* v___y_58_ = stack[9].m_obj;
lean_object* v___y_59_ = stack[10].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0(v_k_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v_b_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v_b_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0(v_k_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v_b_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
return v_res_75_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg(lean_object* v_name_76_, uint8_t v_bi_77_, lean_object* v_type_78_, lean_object* v_k_79_, uint8_t v_kind_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_92_; 
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_91_, 0, v_k_79_);
lean_closure_set(v___f_91_, 1, v___y_81_);
lean_closure_set(v___f_91_, 2, v___y_82_);
lean_closure_set(v___f_91_, 3, v___y_83_);
lean_closure_set(v___f_91_, 4, v___y_84_);
lean_closure_set(v___f_91_, 5, v___y_85_);
v___x_92_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_76_, v_bi_77_, v_type_78_, v___f_91_, v_kind_80_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
if (lean_obj_tag(v___x_92_) == 0)
{
return v___x_92_;
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_76_ = stack[0].m_obj;
uint8_t v_bi_77_ = stack[1].m_num;
lean_object* v_type_78_ = stack[2].m_obj;
lean_object* v_k_79_ = stack[3].m_obj;
uint8_t v_kind_80_ = stack[4].m_num;
lean_object* v___y_81_ = stack[5].m_obj;
lean_object* v___y_82_ = stack[6].m_obj;
lean_object* v___y_83_ = stack[7].m_obj;
lean_object* v___y_84_ = stack[8].m_obj;
lean_object* v___y_85_ = stack[9].m_obj;
lean_object* v___y_86_ = stack[10].m_obj;
lean_object* v___y_87_ = stack[11].m_obj;
lean_object* v___y_88_ = stack[12].m_obj;
lean_object* v___y_89_ = stack[13].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg(v_name_76_, v_bi_77_, v_type_78_, v_k_79_, v_kind_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg___boxed(lean_object* v_name_102_, lean_object* v_bi_103_, lean_object* v_type_104_, lean_object* v_k_105_, lean_object* v_kind_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
uint8_t v_bi_boxed_117_; uint8_t v_kind_boxed_118_; lean_object* v_res_119_; 
v_bi_boxed_117_ = lean_unbox(v_bi_103_);
v_kind_boxed_118_ = lean_unbox(v_kind_106_);
v_res_119_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg(v_name_102_, v_bi_boxed_117_, v_type_104_, v_k_105_, v_kind_boxed_118_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
return v_res_119_;
}
}
lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(lean_object* v_name_120_, uint8_t v_bi_121_, lean_object* v_type_122_, lean_object* v_k_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___f_134_; uint8_t v___x_135_; lean_object* v___x_136_; 
v___f_134_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_134_, 0, v_k_123_);
v___x_135_ = 0;
v___x_136_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg(v_name_120_, v_bi_121_, v_type_122_, v___f_134_, v___x_135_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_120_ = stack[0].m_obj;
uint8_t v_bi_121_ = stack[1].m_num;
lean_object* v_type_122_ = stack[2].m_obj;
lean_object* v_k_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v___y_127_ = stack[7].m_obj;
lean_object* v___y_128_ = stack[8].m_obj;
lean_object* v___y_129_ = stack[9].m_obj;
lean_object* v___y_130_ = stack[10].m_obj;
lean_object* v___y_131_ = stack[11].m_obj;
lean_object* v___y_132_ = stack[12].m_obj;
lean_object* v_res_137_;
v_res_137_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_name_120_, v_bi_121_, v_type_122_, v_k_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___boxed(lean_object* v_name_138_, lean_object* v_bi_139_, lean_object* v_type_140_, lean_object* v_k_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v_bi_boxed_152_; lean_object* v_res_153_; 
v_bi_boxed_152_ = lean_unbox(v_bi_139_);
v_res_153_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_name_138_, v_bi_boxed_152_, v_type_140_, v_k_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0___boxed(lean_object* v_fvars_154_, lean_object* v_body_155_, lean_object* v_modified_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v_modified_boxed_168_; lean_object* v_res_169_; 
v_modified_boxed_168_ = lean_unbox(v_modified_156_);
v_res_169_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0(v_fvars_154_, v_body_155_, v_modified_boxed_168_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
return v_res_169_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1(lean_object* v_fvars_170_, lean_object* v_body_171_, lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_array_push(v_fvars_170_, v_x_172_);
v___x_184_ = 1;
v___x_185_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(v_body_171_, v___x_183_, v___x_184_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
return v___x_185_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_170_ = stack[0].m_obj;
lean_object* v_body_171_ = stack[1].m_obj;
lean_object* v_x_172_ = stack[2].m_obj;
lean_object* v___y_173_ = stack[3].m_obj;
lean_object* v___y_174_ = stack[4].m_obj;
lean_object* v___y_175_ = stack[5].m_obj;
lean_object* v___y_176_ = stack[6].m_obj;
lean_object* v___y_177_ = stack[7].m_obj;
lean_object* v___y_178_ = stack[8].m_obj;
lean_object* v___y_179_ = stack[9].m_obj;
lean_object* v___y_180_ = stack[10].m_obj;
lean_object* v___y_181_ = stack[11].m_obj;
lean_object* v_res_186_;
v_res_186_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1(v_fvars_170_, v_body_171_, v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1___boxed(lean_object* v_fvars_187_, lean_object* v_body_188_, lean_object* v_x_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1(v_fvars_187_, v_body_188_, v_x_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
return v_res_200_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(lean_object* v_e_201_, lean_object* v_fvars_202_, uint8_t v_modified_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
if (lean_obj_tag(v_e_201_) == 7)
{
lean_object* v_binderName_214_; lean_object* v_binderType_215_; lean_object* v_body_216_; uint8_t v_binderInfo_217_; lean_object* v___x_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_221_; 
v_binderName_214_ = lean_ctor_get(v_e_201_, 0);
lean_inc(v_binderName_214_);
v_binderType_215_ = lean_ctor_get(v_e_201_, 1);
lean_inc_ref(v_binderType_215_);
v_body_216_ = lean_ctor_get(v_e_201_, 2);
lean_inc_ref_n(v_body_216_, 2);
v_binderInfo_217_ = lean_ctor_get_uint8(v_e_201_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_201_, 3);
v___x_218_ = lean_box(v_modified_203_);
lean_inc_ref_n(v_fvars_202_, 2);
v___f_219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0___boxed), 14, 3);
lean_closure_set(v___f_219_, 0, v_fvars_202_);
lean_closure_set(v___f_219_, 1, v_body_216_);
lean_closure_set(v___f_219_, 2, v___x_218_);
v___f_220_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_220_, 0, v_fvars_202_);
lean_closure_set(v___f_220_, 1, v_body_216_);
v___x_221_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_binderType_215_, v_fvars_202_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_n(v_a_222_, 2);
lean_dec_ref_known(v___x_221_, 1);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
v___x_223_ = lean_sym_dsimp(v_a_222_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
if (lean_obj_tag(v_a_224_) == 0)
{
lean_object* v___x_225_; 
lean_dec_ref_known(v_a_224_, 0);
lean_dec_ref(v___f_220_);
v___x_225_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_binderName_214_, v_binderInfo_217_, v_a_222_, v___f_219_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
return v___x_225_;
}
else
{
lean_object* v_e_x27_226_; lean_object* v___x_227_; 
lean_dec(v_a_222_);
lean_dec_ref(v___f_219_);
v_e_x27_226_ = lean_ctor_get(v_a_224_, 0);
lean_inc_ref(v_e_x27_226_);
lean_dec_ref_known(v_a_224_, 1);
v___x_227_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_binderName_214_, v_binderInfo_217_, v_e_x27_226_, v___f_220_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
return v___x_227_;
}
}
else
{
lean_dec(v_a_222_);
lean_dec_ref(v___f_220_);
lean_dec_ref(v___f_219_);
lean_dec(v_binderName_214_);
return v___x_223_;
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v___f_220_);
lean_dec_ref(v___f_219_);
lean_dec(v_binderName_214_);
v_a_228_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_221_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v___x_236_; 
lean_inc_ref(v_fvars_202_);
lean_inc_ref(v_e_201_);
v___x_236_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_201_, v_fvars_202_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
v___x_238_ = lean_sym_dsimp(v_a_237_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_298_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_298_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_298_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_298_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
if (lean_obj_tag(v_a_239_) == 0)
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_271_; 
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_239_);
if (v_isSharedCheck_271_ == 0)
{
v___x_244_ = v_a_239_;
v_isShared_245_ = v_isSharedCheck_271_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_a_239_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_271_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
if (v_modified_203_ == 0)
{
lean_object* v___x_247_; 
lean_dec_ref(v_fvars_202_);
lean_dec_ref(v_e_201_);
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 0, 1);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
lean_ctor_set_uint8(v___x_247_, 0, v_modified_203_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_249_ = v___x_241_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v___x_252_; 
lean_del_object(v___x_244_);
lean_del_object(v___x_241_);
v___x_252_ = l_Lean_Meta_Sym_mkForallFVarsS(v_fvars_202_, v_e_201_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_262_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_262_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_262_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_262_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_258_, 0, v_a_253_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_258_);
v___x_260_ = v___x_255_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
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
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_252_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_252_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
}
else
{
lean_object* v_e_x27_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_297_; 
lean_del_object(v___x_241_);
lean_dec_ref(v_e_201_);
v_e_x27_272_ = lean_ctor_get(v_a_239_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_239_);
if (v_isSharedCheck_297_ == 0)
{
v___x_274_ = v_a_239_;
v_isShared_275_ = v_isSharedCheck_297_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_e_x27_272_);
lean_dec(v_a_239_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_297_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Sym_mkForallFVarsS(v_fvars_202_, v_e_x27_272_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_288_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_288_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_288_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_288_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
uint8_t v___x_281_; lean_object* v___x_283_; 
v___x_281_ = 0;
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v_a_277_);
v___x_283_ = v___x_274_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_277_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_281_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_283_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_del_object(v___x_274_);
v_a_289_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_276_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_276_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_fvars_202_);
lean_dec_ref(v_e_201_);
return v___x_238_;
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_fvars_202_);
lean_dec_ref(v_e_201_);
v_a_299_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_236_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_236_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
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
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_201_ = stack[0].m_obj;
lean_object* v_fvars_202_ = stack[1].m_obj;
uint8_t v_modified_203_ = stack[2].m_num;
lean_object* v_a_204_ = stack[3].m_obj;
lean_object* v_a_205_ = stack[4].m_obj;
lean_object* v_a_206_ = stack[5].m_obj;
lean_object* v_a_207_ = stack[6].m_obj;
lean_object* v_a_208_ = stack[7].m_obj;
lean_object* v_a_209_ = stack[8].m_obj;
lean_object* v_a_210_ = stack[9].m_obj;
lean_object* v_a_211_ = stack[10].m_obj;
lean_object* v_a_212_ = stack[11].m_obj;
lean_object* v_res_307_;
v_res_307_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(v_e_201_, v_fvars_202_, v_modified_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
stack->m_obj
 = v_res_307_;
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0(lean_object* v_fvars_308_, lean_object* v_body_309_, uint8_t v_modified_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_array_push(v_fvars_308_, v_x_311_);
v___x_323_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(v_body_309_, v___x_322_, v_modified_310_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_323_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_308_ = stack[0].m_obj;
lean_object* v_body_309_ = stack[1].m_obj;
uint8_t v_modified_310_ = stack[2].m_num;
lean_object* v_x_311_ = stack[3].m_obj;
lean_object* v___y_312_ = stack[4].m_obj;
lean_object* v___y_313_ = stack[5].m_obj;
lean_object* v___y_314_ = stack[6].m_obj;
lean_object* v___y_315_ = stack[7].m_obj;
lean_object* v___y_316_ = stack[8].m_obj;
lean_object* v___y_317_ = stack[9].m_obj;
lean_object* v___y_318_ = stack[10].m_obj;
lean_object* v___y_319_ = stack[11].m_obj;
lean_object* v___y_320_ = stack[12].m_obj;
lean_object* v_res_324_;
v_res_324_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0(v_fvars_308_, v_body_309_, v_modified_310_, v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___boxed(lean_object* v_e_325_, lean_object* v_fvars_326_, lean_object* v_modified_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
uint8_t v_modified_boxed_338_; lean_object* v_res_339_; 
v_modified_boxed_338_ = lean_unbox(v_modified_327_);
v_res_339_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(v_e_325_, v_fvars_326_, v_modified_boxed_338_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
return v_res_339_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0(lean_object* v_fvarId_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___redArg(v_fvarId_340_, v___y_342_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_340_ = stack[0].m_obj;
lean_object* v___y_341_ = stack[1].m_obj;
lean_object* v___y_342_ = stack[2].m_obj;
lean_object* v___y_343_ = stack[3].m_obj;
lean_object* v___y_344_ = stack[4].m_obj;
lean_object* v___y_345_ = stack[5].m_obj;
lean_object* v___y_346_ = stack[6].m_obj;
lean_object* v_res_349_;
v_res_349_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0(v_fvarId_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0___boxed(lean_object* v_fvarId_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__0(v_fvarId_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_358_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1(lean_object* v_00_u03b1_359_, lean_object* v_name_360_, uint8_t v_bi_361_, lean_object* v_type_362_, lean_object* v_k_363_, uint8_t v_kind_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___redArg(v_name_360_, v_bi_361_, v_type_362_, v_k_363_, v_kind_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_360_ = stack[1].m_obj;
uint8_t v_bi_361_ = stack[2].m_num;
lean_object* v_type_362_ = stack[3].m_obj;
lean_object* v_k_363_ = stack[4].m_obj;
uint8_t v_kind_364_ = stack[5].m_num;
lean_object* v___y_365_ = stack[6].m_obj;
lean_object* v___y_366_ = stack[7].m_obj;
lean_object* v___y_367_ = stack[8].m_obj;
lean_object* v___y_368_ = stack[9].m_obj;
lean_object* v___y_369_ = stack[10].m_obj;
lean_object* v___y_370_ = stack[11].m_obj;
lean_object* v___y_371_ = stack[12].m_obj;
lean_object* v___y_372_ = stack[13].m_obj;
lean_object* v___y_373_ = stack[14].m_obj;
lean_object* v_res_376_;
v_res_376_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1(lean_box(0), v_name_360_, v_bi_361_, v_type_362_, v_k_363_, v_kind_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
stack->m_obj
 = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1___boxed(lean_object* v_00_u03b1_377_, lean_object* v_name_378_, lean_object* v_bi_379_, lean_object* v_type_380_, lean_object* v_k_381_, lean_object* v_kind_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
uint8_t v_bi_boxed_393_; uint8_t v_kind_boxed_394_; lean_object* v_res_395_; 
v_bi_boxed_393_ = lean_unbox(v_bi_379_);
v_kind_boxed_394_ = lean_unbox(v_kind_382_);
v_res_395_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_spec__1(v_00_u03b1_377_, v_name_378_, v_bi_boxed_393_, v_type_380_, v_k_381_, v_kind_boxed_394_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
return v_res_395_;
}
}
lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0(lean_object* v_00_u03b1_396_, lean_object* v_name_397_, uint8_t v_bi_398_, lean_object* v_type_399_, lean_object* v_k_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_name_397_, v_bi_398_, v_type_399_, v_k_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_411_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_397_ = stack[1].m_obj;
uint8_t v_bi_398_ = stack[2].m_num;
lean_object* v_type_399_ = stack[3].m_obj;
lean_object* v_k_400_ = stack[4].m_obj;
lean_object* v___y_401_ = stack[5].m_obj;
lean_object* v___y_402_ = stack[6].m_obj;
lean_object* v___y_403_ = stack[7].m_obj;
lean_object* v___y_404_ = stack[8].m_obj;
lean_object* v___y_405_ = stack[9].m_obj;
lean_object* v___y_406_ = stack[10].m_obj;
lean_object* v___y_407_ = stack[11].m_obj;
lean_object* v___y_408_ = stack[12].m_obj;
lean_object* v___y_409_ = stack[13].m_obj;
lean_object* v_res_412_;
v_res_412_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0(lean_box(0), v_name_397_, v_bi_398_, v_type_399_, v_k_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_name_414_, lean_object* v_bi_415_, lean_object* v_type_416_, lean_object* v_k_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v_bi_boxed_428_; lean_object* v_res_429_; 
v_bi_boxed_428_ = lean_unbox(v_bi_415_);
v_res_429_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0(v_00_u03b1_413_, v_name_414_, v_bi_boxed_428_, v_type_416_, v_k_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
return v_res_429_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0));
v___x_444_ = 0;
v___x_445_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(v_e_432_, v___x_443_, v___x_444_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_432_ = stack[0].m_obj;
lean_object* v_a_433_ = stack[1].m_obj;
lean_object* v_a_434_ = stack[2].m_obj;
lean_object* v_a_435_ = stack[3].m_obj;
lean_object* v_a_436_ = stack[4].m_obj;
lean_object* v_a_437_ = stack[5].m_obj;
lean_object* v_a_438_ = stack[6].m_obj;
lean_object* v_a_439_ = stack[7].m_obj;
lean_object* v_a_440_ = stack[8].m_obj;
lean_object* v_a_441_ = stack[9].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_Meta_Sym_DSimp_dsimpForall(v_e_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpForall___boxed(lean_object* v_e_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_Sym_DSimp_dsimpForall(v_e_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
return v_res_458_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin) {
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
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Forall(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
}
#ifdef __cplusplus
}
#endif
