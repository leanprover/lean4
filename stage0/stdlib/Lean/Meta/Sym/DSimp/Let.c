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
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v_b_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
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
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_b_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v___y_11_ = stack[10].m_obj;
lean_object* v_res_14_;
v_res_14_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0(v_k_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v_b_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v_b_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0(v_k_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v_b_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
return v_res_27_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(lean_object* v_name_28_, lean_object* v_type_29_, lean_object* v_val_30_, lean_object* v_k_31_, uint8_t v_nondep_32_, uint8_t v_kind_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; 
lean_inc(v___y_38_);
lean_inc_ref(v___y_37_);
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
lean_inc(v___y_34_);
v___f_44_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_44_, 0, v_k_31_);
lean_closure_set(v___f_44_, 1, v___y_34_);
lean_closure_set(v___f_44_, 2, v___y_35_);
lean_closure_set(v___f_44_, 3, v___y_36_);
lean_closure_set(v___f_44_, 4, v___y_37_);
lean_closure_set(v___f_44_, 5, v___y_38_);
v___x_45_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_28_, v_type_29_, v_val_30_, v___f_44_, v_nondep_32_, v_kind_33_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_45_) == 0)
{
return v___x_45_;
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_28_ = stack[0].m_obj;
lean_object* v_type_29_ = stack[1].m_obj;
lean_object* v_val_30_ = stack[2].m_obj;
lean_object* v_k_31_ = stack[3].m_obj;
uint8_t v_nondep_32_ = stack[4].m_num;
uint8_t v_kind_33_ = stack[5].m_num;
lean_object* v___y_34_ = stack[6].m_obj;
lean_object* v___y_35_ = stack[7].m_obj;
lean_object* v___y_36_ = stack[8].m_obj;
lean_object* v___y_37_ = stack[9].m_obj;
lean_object* v___y_38_ = stack[10].m_obj;
lean_object* v___y_39_ = stack[11].m_obj;
lean_object* v___y_40_ = stack[12].m_obj;
lean_object* v___y_41_ = stack[13].m_obj;
lean_object* v___y_42_ = stack[14].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_28_, v_type_29_, v_val_30_, v_k_31_, v_nondep_32_, v_kind_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg___boxed(lean_object* v_name_55_, lean_object* v_type_56_, lean_object* v_val_57_, lean_object* v_k_58_, lean_object* v_nondep_59_, lean_object* v_kind_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
uint8_t v_nondep_boxed_71_; uint8_t v_kind_boxed_72_; lean_object* v_res_73_; 
v_nondep_boxed_71_ = lean_unbox(v_nondep_59_);
v_kind_boxed_72_ = lean_unbox(v_kind_60_);
v_res_73_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_55_, v_type_56_, v_val_57_, v_k_58_, v_nondep_boxed_71_, v_kind_boxed_72_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
return v_res_73_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(lean_object* v_fvarId_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l_Lean_Expr_fvar___override(v_fvarId_74_);
v___x_78_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_77_, v___y_75_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_74_ = stack[0].m_obj;
lean_object* v___y_75_ = stack[1].m_obj;
lean_object* v_res_79_;
v_res_79_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v_fvarId_74_, v___y_75_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v_fvarId_80_, v___y_81_);
lean_dec(v___y_81_);
return v_res_83_;
}
}
lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(lean_object* v_k_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = l_Lean_Expr_fvarId_x21(v_x_85_);
v___x_97_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v___x_96_, v___y_90_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
lean_inc(v___y_94_);
lean_inc_ref(v___y_93_);
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
v___x_99_ = lean_apply_11(v_k_84_, v_a_98_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, lean_box(0));
return v___x_99_;
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec_ref(v_k_84_);
v_a_100_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_97_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_84_ = stack[0].m_obj;
lean_object* v_x_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v___y_93_ = stack[9].m_obj;
lean_object* v___y_94_ = stack[10].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_84_, v_x_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_109_, v_x_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v_x_110_);
return v_res_121_;
}
}
lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(lean_object* v_name_122_, lean_object* v_type_123_, lean_object* v_val_124_, lean_object* v_k_125_, uint8_t v_nondep_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___f_137_; uint8_t v___x_138_; lean_object* v___x_139_; 
v___f_137_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_137_, 0, v_k_125_);
v___x_138_ = 0;
v___x_139_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_122_, v_type_123_, v_val_124_, v___f_137_, v_nondep_126_, v___x_138_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_122_ = stack[0].m_obj;
lean_object* v_type_123_ = stack[1].m_obj;
lean_object* v_val_124_ = stack[2].m_obj;
lean_object* v_k_125_ = stack[3].m_obj;
uint8_t v_nondep_126_ = stack[4].m_num;
lean_object* v___y_127_ = stack[5].m_obj;
lean_object* v___y_128_ = stack[6].m_obj;
lean_object* v___y_129_ = stack[7].m_obj;
lean_object* v___y_130_ = stack[8].m_obj;
lean_object* v___y_131_ = stack[9].m_obj;
lean_object* v___y_132_ = stack[10].m_obj;
lean_object* v___y_133_ = stack[11].m_obj;
lean_object* v___y_134_ = stack[12].m_obj;
lean_object* v___y_135_ = stack[13].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_122_, v_type_123_, v_val_124_, v_k_125_, v_nondep_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___boxed(lean_object* v_name_141_, lean_object* v_type_142_, lean_object* v_val_143_, lean_object* v_k_144_, lean_object* v_nondep_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_nondep_boxed_156_; lean_object* v_res_157_; 
v_nondep_boxed_156_ = lean_unbox(v_nondep_145_);
v_res_157_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_141_, v_type_142_, v_val_143_, v_k_144_, v_nondep_boxed_156_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(lean_object* v_fvars_158_, lean_object* v_body_159_, lean_object* v_modified_160_, lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v_modified_boxed_172_; lean_object* v_res_173_; 
v_modified_boxed_172_ = lean_unbox(v_modified_160_);
v_res_173_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(v_fvars_158_, v_body_159_, v_modified_boxed_172_, v_x_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
return v_res_173_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(lean_object* v_fvars_174_, lean_object* v_body_175_, lean_object* v_x_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_array_push(v_fvars_174_, v_x_176_);
v___x_188_ = 1;
v___x_189_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_body_175_, v___x_187_, v___x_188_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_189_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_174_ = stack[0].m_obj;
lean_object* v_body_175_ = stack[1].m_obj;
lean_object* v_x_176_ = stack[2].m_obj;
lean_object* v___y_177_ = stack[3].m_obj;
lean_object* v___y_178_ = stack[4].m_obj;
lean_object* v___y_179_ = stack[5].m_obj;
lean_object* v___y_180_ = stack[6].m_obj;
lean_object* v___y_181_ = stack[7].m_obj;
lean_object* v___y_182_ = stack[8].m_obj;
lean_object* v___y_183_ = stack[9].m_obj;
lean_object* v___y_184_ = stack[10].m_obj;
lean_object* v___y_185_ = stack[11].m_obj;
lean_object* v_res_190_;
v_res_190_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(v_fvars_174_, v_body_175_, v_x_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed(lean_object* v_fvars_191_, lean_object* v_body_192_, lean_object* v_x_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(v_fvars_191_, v_body_192_, v_x_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
return v_res_204_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(lean_object* v_e_205_, lean_object* v_fvars_206_, uint8_t v_modified_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
if (lean_obj_tag(v_e_205_) == 8)
{
lean_object* v_declName_218_; lean_object* v_type_219_; lean_object* v_value_220_; lean_object* v_body_221_; uint8_t v_nondep_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; 
v_declName_218_ = lean_ctor_get(v_e_205_, 0);
lean_inc(v_declName_218_);
v_type_219_ = lean_ctor_get(v_e_205_, 1);
lean_inc_ref(v_type_219_);
v_value_220_ = lean_ctor_get(v_e_205_, 2);
lean_inc_ref(v_value_220_);
v_body_221_ = lean_ctor_get(v_e_205_, 3);
lean_inc_ref_n(v_body_221_, 2);
v_nondep_222_ = lean_ctor_get_uint8(v_e_205_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_205_, 4);
v___x_223_ = lean_box(v_modified_207_);
lean_inc_ref_n(v_fvars_206_, 3);
v___f_224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed), 14, 3);
lean_closure_set(v___f_224_, 0, v_fvars_206_);
lean_closure_set(v___f_224_, 1, v_body_221_);
lean_closure_set(v___f_224_, 2, v___x_223_);
v___f_225_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_225_, 0, v_fvars_206_);
lean_closure_set(v___f_225_, 1, v_body_221_);
v___x_226_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_type_219_, v_fvars_206_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_value_220_, v_fvars_206_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc(v_a_227_);
v___x_230_ = lean_sym_dsimp(v_a_227_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc(v_a_229_);
v___x_232_ = lean_sym_dsimp(v_a_229_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_232_) == 0)
{
if (lean_obj_tag(v_a_231_) == 0)
{
lean_object* v_a_233_; 
lean_dec_ref_known(v_a_231_, 0);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
if (lean_obj_tag(v_a_233_) == 0)
{
lean_object* v___x_234_; 
lean_dec_ref_known(v_a_233_, 0);
lean_dec_ref(v___f_225_);
v___x_234_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_218_, v_a_227_, v_a_229_, v___f_224_, v_nondep_222_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_234_;
}
else
{
lean_object* v_e_x27_235_; lean_object* v___x_236_; 
lean_dec(v_a_229_);
lean_dec_ref(v___f_224_);
v_e_x27_235_ = lean_ctor_get(v_a_233_, 0);
lean_inc_ref(v_e_x27_235_);
lean_dec_ref_known(v_a_233_, 1);
v___x_236_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_218_, v_a_227_, v_e_x27_235_, v___f_225_, v_nondep_222_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_236_;
}
}
else
{
lean_object* v_a_237_; 
lean_dec(v_a_227_);
lean_dec_ref(v___f_224_);
v_a_237_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_232_, 1);
if (lean_obj_tag(v_a_237_) == 0)
{
lean_object* v_e_x27_238_; lean_object* v___x_239_; 
lean_dec_ref_known(v_a_237_, 0);
v_e_x27_238_ = lean_ctor_get(v_a_231_, 0);
lean_inc_ref(v_e_x27_238_);
lean_dec_ref_known(v_a_231_, 1);
v___x_239_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_218_, v_e_x27_238_, v_a_229_, v___f_225_, v_nondep_222_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_239_;
}
else
{
lean_object* v_e_x27_240_; lean_object* v_e_x27_241_; lean_object* v___x_242_; 
lean_dec(v_a_229_);
v_e_x27_240_ = lean_ctor_get(v_a_231_, 0);
lean_inc_ref(v_e_x27_240_);
lean_dec_ref_known(v_a_231_, 1);
v_e_x27_241_ = lean_ctor_get(v_a_237_, 0);
lean_inc_ref(v_e_x27_241_);
lean_dec_ref_known(v_a_237_, 1);
v___x_242_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_218_, v_e_x27_240_, v_e_x27_241_, v___f_225_, v_nondep_222_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_242_;
}
}
}
else
{
lean_dec(v_a_231_);
lean_dec(v_a_229_);
lean_dec(v_a_227_);
lean_dec_ref(v___f_225_);
lean_dec_ref(v___f_224_);
lean_dec(v_declName_218_);
return v___x_232_;
}
}
else
{
lean_dec(v_a_229_);
lean_dec(v_a_227_);
lean_dec_ref(v___f_225_);
lean_dec_ref(v___f_224_);
lean_dec(v_declName_218_);
return v___x_230_;
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_227_);
lean_dec_ref(v___f_225_);
lean_dec_ref(v___f_224_);
lean_dec(v_declName_218_);
v_a_243_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_228_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_228_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v___f_225_);
lean_dec_ref(v___f_224_);
lean_dec_ref(v_value_220_);
lean_dec(v_declName_218_);
lean_dec_ref(v_fvars_206_);
v_a_251_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_226_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_226_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v___x_259_; 
lean_inc_ref(v_fvars_206_);
lean_inc_ref(v_e_205_);
v___x_259_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_205_, v_fvars_206_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
v___x_261_ = lean_sym_dsimp(v_a_260_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_323_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_323_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_323_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_323_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
if (lean_obj_tag(v_a_262_) == 0)
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_262_);
if (v_isSharedCheck_295_ == 0)
{
v___x_267_ = v_a_262_;
v_isShared_268_ = v_isSharedCheck_295_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_a_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_295_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
if (v_modified_207_ == 0)
{
lean_object* v___x_270_; 
lean_dec_ref(v_fvars_206_);
lean_dec_ref(v_e_205_);
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 0, 1);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_272_; 
lean_ctor_set_uint8(v___x_270_, 0, v_modified_207_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_272_ = v___x_264_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
uint8_t v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
lean_del_object(v___x_267_);
lean_del_object(v___x_264_);
v___x_275_ = 0;
v___x_276_ = 1;
v___x_277_ = l_Lean_Meta_mkLetFVars(v_fvars_206_, v_e_205_, v___x_275_, v___x_275_, v___x_276_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec_ref(v_fvars_206_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_282_, 0, v_a_278_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_275_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_277_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_277_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
else
{
lean_object* v_e_x27_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_322_; 
lean_del_object(v___x_264_);
lean_dec_ref(v_e_205_);
v_e_x27_296_ = lean_ctor_get(v_a_262_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_262_);
if (v_isSharedCheck_322_ == 0)
{
v___x_298_ = v_a_262_;
v_isShared_299_ = v_isSharedCheck_322_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_e_x27_296_);
lean_dec(v_a_262_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_322_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint8_t v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; 
v___x_300_ = 0;
v___x_301_ = 1;
v___x_302_ = l_Lean_Meta_mkLetFVars(v_fvars_206_, v_e_x27_296_, v___x_300_, v___x_300_, v___x_301_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec_ref(v_fvars_206_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_313_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_313_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_313_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_a_303_);
v___x_308_ = v___x_298_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_300_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_del_object(v___x_298_);
v_a_314_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_302_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_302_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_fvars_206_);
lean_dec_ref(v_e_205_);
return v___x_261_;
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_fvars_206_);
lean_dec_ref(v_e_205_);
v_a_324_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_259_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_259_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_205_ = stack[0].m_obj;
lean_object* v_fvars_206_ = stack[1].m_obj;
uint8_t v_modified_207_ = stack[2].m_num;
lean_object* v_a_208_ = stack[3].m_obj;
lean_object* v_a_209_ = stack[4].m_obj;
lean_object* v_a_210_ = stack[5].m_obj;
lean_object* v_a_211_ = stack[6].m_obj;
lean_object* v_a_212_ = stack[7].m_obj;
lean_object* v_a_213_ = stack[8].m_obj;
lean_object* v_a_214_ = stack[9].m_obj;
lean_object* v_a_215_ = stack[10].m_obj;
lean_object* v_a_216_ = stack[11].m_obj;
lean_object* v_res_332_;
v_res_332_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_205_, v_fvars_206_, v_modified_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
stack->m_obj
 = v_res_332_;
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(lean_object* v_fvars_333_, lean_object* v_body_334_, uint8_t v_modified_335_, lean_object* v_x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_array_push(v_fvars_333_, v_x_336_);
v___x_348_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_body_334_, v___x_347_, v_modified_335_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_348_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_333_ = stack[0].m_obj;
lean_object* v_body_334_ = stack[1].m_obj;
uint8_t v_modified_335_ = stack[2].m_num;
lean_object* v_x_336_ = stack[3].m_obj;
lean_object* v___y_337_ = stack[4].m_obj;
lean_object* v___y_338_ = stack[5].m_obj;
lean_object* v___y_339_ = stack[6].m_obj;
lean_object* v___y_340_ = stack[7].m_obj;
lean_object* v___y_341_ = stack[8].m_obj;
lean_object* v___y_342_ = stack[9].m_obj;
lean_object* v___y_343_ = stack[10].m_obj;
lean_object* v___y_344_ = stack[11].m_obj;
lean_object* v___y_345_ = stack[12].m_obj;
lean_object* v_res_349_;
v_res_349_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(v_fvars_333_, v_body_334_, v_modified_335_, v_x_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___boxed(lean_object* v_e_350_, lean_object* v_fvars_351_, lean_object* v_modified_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
uint8_t v_modified_boxed_363_; lean_object* v_res_364_; 
v_modified_boxed_363_ = lean_unbox(v_modified_352_);
v_res_364_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_350_, v_fvars_351_, v_modified_boxed_363_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
return v_res_364_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0(lean_object* v_fvarId_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___redArg(v_fvarId_365_, v___y_367_);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_365_ = stack[0].m_obj;
lean_object* v___y_366_ = stack[1].m_obj;
lean_object* v___y_367_ = stack[2].m_obj;
lean_object* v___y_368_ = stack[3].m_obj;
lean_object* v___y_369_ = stack[4].m_obj;
lean_object* v___y_370_ = stack[5].m_obj;
lean_object* v___y_371_ = stack[6].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0(v_fvarId_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0___boxed(lean_object* v_fvarId_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__0(v_fvarId_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_383_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1(lean_object* v_00_u03b1_384_, lean_object* v_name_385_, lean_object* v_type_386_, lean_object* v_val_387_, lean_object* v_k_388_, uint8_t v_nondep_389_, uint8_t v_kind_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___redArg(v_name_385_, v_type_386_, v_val_387_, v_k_388_, v_nondep_389_, v_kind_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_385_ = stack[1].m_obj;
lean_object* v_type_386_ = stack[2].m_obj;
lean_object* v_val_387_ = stack[3].m_obj;
lean_object* v_k_388_ = stack[4].m_obj;
uint8_t v_nondep_389_ = stack[5].m_num;
uint8_t v_kind_390_ = stack[6].m_num;
lean_object* v___y_391_ = stack[7].m_obj;
lean_object* v___y_392_ = stack[8].m_obj;
lean_object* v___y_393_ = stack[9].m_obj;
lean_object* v___y_394_ = stack[10].m_obj;
lean_object* v___y_395_ = stack[11].m_obj;
lean_object* v___y_396_ = stack[12].m_obj;
lean_object* v___y_397_ = stack[13].m_obj;
lean_object* v___y_398_ = stack[14].m_obj;
lean_object* v___y_399_ = stack[15].m_obj;
lean_object* v_res_402_;
v_res_402_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1(lean_box(0), v_name_385_, v_type_386_, v_val_387_, v_k_388_, v_nondep_389_, v_kind_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_00_u03b1_403_ = _args[0];
lean_object* v_name_404_ = _args[1];
lean_object* v_type_405_ = _args[2];
lean_object* v_val_406_ = _args[3];
lean_object* v_k_407_ = _args[4];
lean_object* v_nondep_408_ = _args[5];
lean_object* v_kind_409_ = _args[6];
lean_object* v___y_410_ = _args[7];
lean_object* v___y_411_ = _args[8];
lean_object* v___y_412_ = _args[9];
lean_object* v___y_413_ = _args[10];
lean_object* v___y_414_ = _args[11];
lean_object* v___y_415_ = _args[12];
lean_object* v___y_416_ = _args[13];
lean_object* v___y_417_ = _args[14];
lean_object* v___y_418_ = _args[15];
lean_object* v___y_419_ = _args[16];
_start:
{
uint8_t v_nondep_boxed_420_; uint8_t v_kind_boxed_421_; lean_object* v_res_422_; 
v_nondep_boxed_420_ = lean_unbox(v_nondep_408_);
v_kind_boxed_421_ = lean_unbox(v_kind_409_);
v_res_422_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_spec__1(v_00_u03b1_403_, v_name_404_, v_type_405_, v_val_406_, v_k_407_, v_nondep_boxed_420_, v_kind_boxed_421_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
return v_res_422_;
}
}
lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(lean_object* v_00_u03b1_423_, lean_object* v_name_424_, lean_object* v_type_425_, lean_object* v_val_426_, lean_object* v_k_427_, uint8_t v_nondep_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_424_, v_type_425_, v_val_426_, v_k_427_, v_nondep_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
return v___x_439_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_424_ = stack[1].m_obj;
lean_object* v_type_425_ = stack[2].m_obj;
lean_object* v_val_426_ = stack[3].m_obj;
lean_object* v_k_427_ = stack[4].m_obj;
uint8_t v_nondep_428_ = stack[5].m_num;
lean_object* v___y_429_ = stack[6].m_obj;
lean_object* v___y_430_ = stack[7].m_obj;
lean_object* v___y_431_ = stack[8].m_obj;
lean_object* v___y_432_ = stack[9].m_obj;
lean_object* v___y_433_ = stack[10].m_obj;
lean_object* v___y_434_ = stack[11].m_obj;
lean_object* v___y_435_ = stack[12].m_obj;
lean_object* v___y_436_ = stack[13].m_obj;
lean_object* v___y_437_ = stack[14].m_obj;
lean_object* v_res_440_;
v_res_440_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(lean_box(0), v_name_424_, v_type_425_, v_val_426_, v_k_427_, v_nondep_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(lean_object* v_00_u03b1_441_, lean_object* v_name_442_, lean_object* v_type_443_, lean_object* v_val_444_, lean_object* v_k_445_, lean_object* v_nondep_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v_nondep_boxed_457_; lean_object* v_res_458_; 
v_nondep_boxed_457_ = lean_unbox(v_nondep_446_);
v_res_458_ = l_Lean_Meta_Sym_withLetDeclS___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(v_00_u03b1_441_, v_name_442_, v_type_443_, v_val_444_, v_k_445_, v_nondep_boxed_457_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
return v_res_458_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0));
v___x_473_ = 0;
v___x_474_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_461_, v___x_472_, v___x_473_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
return v___x_474_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_dsimpLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_461_ = stack[0].m_obj;
lean_object* v_a_462_ = stack[1].m_obj;
lean_object* v_a_463_ = stack[2].m_obj;
lean_object* v_a_464_ = stack[3].m_obj;
lean_object* v_a_465_ = stack[4].m_obj;
lean_object* v_a_466_ = stack[5].m_obj;
lean_object* v_a_467_ = stack[6].m_obj;
lean_object* v_a_468_ = stack[7].m_obj;
lean_object* v_a_469_ = stack[8].m_obj;
lean_object* v_a_470_ = stack[9].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(lean_object* v_e_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
return v_res_487_;
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
