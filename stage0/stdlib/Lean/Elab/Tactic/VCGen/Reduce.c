// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Reduce
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.WHNF import Lean.Meta.Sym.Util import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AlphaShareBuilder
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
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_projectCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
if (lean_obj_tag(v_e_1_) == 11)
{
lean_object* v_idx_7_; lean_object* v_struct_8_; lean_object* v___x_9_; 
v_idx_7_ = lean_ctor_get(v_e_1_, 1);
lean_inc(v_idx_7_);
v_struct_8_ = lean_ctor_get(v_e_1_, 2);
lean_inc_ref_n(v_struct_8_, 2);
lean_dec_ref_known(v_e_1_, 3);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
lean_inc_ref(v_a_2_);
v___x_9_ = lean_whnf(v_struct_8_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_n(v_a_10_, 2);
lean_dec_ref_known(v___x_9_, 1);
v___x_11_ = l_Lean_Meta_projectCore_x3f(v_a_10_, v_idx_7_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
lean_dec(v_idx_7_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
if (lean_obj_tag(v_a_12_) == 1)
{
lean_object* v_val_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_40_; 
v_val_13_ = lean_ctor_get(v_a_12_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v_a_12_);
if (v_isSharedCheck_40_ == 0)
{
v___x_15_ = v_a_12_;
v_isShared_16_ = v_isSharedCheck_40_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_val_13_);
lean_dec(v_a_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_40_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
size_t v___x_17_; size_t v___x_18_; uint8_t v___x_19_; 
v___x_17_ = lean_ptr_addr(v_struct_8_);
lean_dec_ref(v_struct_8_);
v___x_18_ = lean_ptr_addr(v_a_10_);
lean_dec(v_a_10_);
v___x_19_ = lean_usize_dec_eq(v___x_17_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_dec_ref_known(v___x_11_, 1);
v___x_20_ = l_Lean_Meta_Sym_unfoldReducible(v_val_13_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_31_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_31_ == 0)
{
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_31_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_31_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_a_21_);
v___x_26_ = v___x_15_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_30_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_28_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_26_);
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
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
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_del_object(v___x_15_);
v_a_32_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_20_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_20_);
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
else
{
lean_del_object(v___x_15_);
lean_dec(v_val_13_);
return v___x_11_;
}
}
}
else
{
lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_12_);
lean_dec(v_a_10_);
lean_dec_ref(v_struct_8_);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_48_ == 0)
{
lean_object* v_unused_49_; 
v_unused_49_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_49_);
v___x_42_ = v___x_11_;
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
else
{
lean_dec(v___x_11_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_48_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_box(0);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_44_);
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
else
{
lean_dec(v_a_10_);
lean_dec_ref(v_struct_8_);
return v___x_11_;
}
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
lean_dec_ref(v_struct_8_);
lean_dec(v_idx_7_);
v_a_50_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_9_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_9_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec_ref(v_e_1_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_60_;
v_res_60_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object* v_e_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_e_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
return v_res_67_;
}
}
lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(lean_object* v_declName_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_env_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_71_);
v___x_73_ = l_Lean_Environment_isProjectionFn(v_env_72_, v_declName_68_);
v___x_74_ = lean_box(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_68_ = stack[0].m_obj;
lean_object* v___y_69_ = stack[1].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_68_, v___y_69_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg___boxed(lean_object* v_declName_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_77_, v___y_78_);
lean_dec(v___y_78_);
return v_res_80_;
}
}
lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(lean_object* v_declName_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_81_, v___y_87_);
return v___x_89_;
}
}
LEAN_EXPORT void l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_81_ = stack[0].m_obj;
lean_object* v___y_82_ = stack[1].m_obj;
lean_object* v___y_83_ = stack[2].m_obj;
lean_object* v___y_84_ = stack[3].m_obj;
lean_object* v___y_85_ = stack[4].m_obj;
lean_object* v___y_86_ = stack[5].m_obj;
lean_object* v___y_87_ = stack[6].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(v_declName_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___boxed(lean_object* v_declName_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(v_declName_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_99_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(lean_object* v_f_100_, lean_object* v_a_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___y_110_; lean_object* v___x_113_; uint8_t v_debug_114_; 
v___x_113_ = lean_st_ref_get(v___y_103_);
v_debug_114_ = lean_ctor_get_uint8(v___x_113_, sizeof(void*)*12);
lean_dec(v___x_113_);
if (v_debug_114_ == 0)
{
v___y_110_ = v___y_103_;
goto v___jp_109_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_100_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_dec_ref_known(v___x_116_, 1);
v___y_110_ = v___y_103_;
goto v___jp_109_;
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v_a_101_);
lean_dec_ref(v_f_100_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_a_101_);
lean_dec_ref(v_f_100_);
v_a_125_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_115_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_115_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = l_Lean_Expr_app___override(v_f_100_, v_a_101_);
v___x_112_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_111_, v___y_110_);
return v___x_112_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_100_ = stack[0].m_obj;
lean_object* v_a_101_ = stack[1].m_obj;
lean_object* v___y_102_ = stack[2].m_obj;
lean_object* v___y_103_ = stack[3].m_obj;
lean_object* v___y_104_ = stack[4].m_obj;
lean_object* v___y_105_ = stack[5].m_obj;
lean_object* v___y_106_ = stack[6].m_obj;
lean_object* v___y_107_ = stack[7].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(v_f_100_, v_a_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2___boxed(lean_object* v_f_134_, lean_object* v_a_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(v_f_134_, v_a_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_143_;
}
}
lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(lean_object* v_revArgs_144_, lean_object* v_start_145_, lean_object* v_b_146_, lean_object* v_i_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_le(v_i_147_, v_start_145_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_i_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = l_Lean_instInhabitedExpr;
v___x_157_ = lean_unsigned_to_nat(1u);
v_i_158_ = lean_nat_sub(v_i_147_, v___x_157_);
lean_dec(v_i_147_);
v___x_159_ = lean_array_get_borrowed(v___x_156_, v_revArgs_144_, v_i_158_);
lean_inc(v___x_159_);
v___x_160_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(v_b_146_, v___x_159_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v_b_146_ = v_a_161_;
v_i_147_ = v_i_158_;
goto _start;
}
else
{
lean_dec(v_i_158_);
return v___x_160_;
}
}
else
{
lean_object* v___x_163_; 
lean_dec(v_i_147_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v_b_146_);
return v___x_163_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_revArgs_144_ = stack[0].m_obj;
lean_object* v_start_145_ = stack[1].m_obj;
lean_object* v_b_146_ = stack[2].m_obj;
lean_object* v_i_147_ = stack[3].m_obj;
lean_object* v___y_148_ = stack[4].m_obj;
lean_object* v___y_149_ = stack[5].m_obj;
lean_object* v___y_150_ = stack[6].m_obj;
lean_object* v___y_151_ = stack[7].m_obj;
lean_object* v___y_152_ = stack[8].m_obj;
lean_object* v___y_153_ = stack[9].m_obj;
lean_object* v_res_164_;
v_res_164_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_144_, v_start_145_, v_b_146_, v_i_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0___boxed(lean_object* v_revArgs_165_, lean_object* v_start_166_, lean_object* v_b_167_, lean_object* v_i_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_165_, v_start_166_, v_b_167_, v_i_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v_start_166_);
lean_dec_ref(v_revArgs_165_);
return v_res_176_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(lean_object* v_f_177_, lean_object* v_revArgs_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_array_get_size(v_revArgs_178_);
v___x_188_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_178_, v___x_186_, v_f_177_, v___x_187_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_188_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_177_ = stack[0].m_obj;
lean_object* v_revArgs_178_ = stack[1].m_obj;
lean_object* v___y_179_ = stack[2].m_obj;
lean_object* v___y_180_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[4].m_obj;
lean_object* v___y_182_ = stack[5].m_obj;
lean_object* v___y_183_ = stack[6].m_obj;
lean_object* v___y_184_ = stack[7].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_f_177_, v_revArgs_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object* v_f_190_, lean_object* v_revArgs_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_f_190_, v_revArgs_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec_ref(v_revArgs_191_);
return v_res_199_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(lean_object* v_lastReduction_200_, lean_object* v_f_201_, lean_object* v_rargs_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___y_211_; 
switch(lean_obj_tag(v_f_201_))
{
case 10:
{
lean_object* v_expr_261_; 
v_expr_261_ = lean_ctor_get(v_f_201_, 1);
lean_inc_ref(v_expr_261_);
lean_dec_ref_known(v_f_201_, 2);
v_f_201_ = v_expr_261_;
goto _start;
}
case 5:
{
lean_object* v_fn_263_; lean_object* v_arg_264_; lean_object* v___x_265_; 
v_fn_263_ = lean_ctor_get(v_f_201_, 0);
lean_inc_ref(v_fn_263_);
v_arg_264_ = lean_ctor_get(v_f_201_, 1);
lean_inc_ref(v_arg_264_);
lean_dec_ref_known(v_f_201_, 2);
v___x_265_ = lean_array_push(v_rargs_202_, v_arg_264_);
v_f_201_ = v_fn_263_;
v_rargs_202_ = v___x_265_;
goto _start;
}
case 6:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = lean_array_get_size(v_rargs_202_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v_lastReduction_200_);
v___x_270_ = l_Lean_Meta_Sym_betaRevS(v_f_201_, v_rargs_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_n(v_a_271_, 2);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_a_271_);
v___x_273_ = l_Lean_Expr_getAppFn(v_a_271_);
v___x_274_ = l_Lean_Expr_getAppNumArgs(v_a_271_);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
lean_dec(v___x_274_);
v___x_276_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_271_, v___x_275_);
v_lastReduction_200_ = v___x_272_;
v_f_201_ = v___x_273_;
v_rargs_202_ = v___x_276_;
goto _start;
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_270_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_270_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v___x_286_; 
lean_dec_ref_known(v_f_201_, 3);
lean_dec_ref(v_rargs_202_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_lastReduction_200_);
return v___x_286_;
}
}
case 4:
{
lean_object* v_declName_287_; lean_object* v___x_288_; 
v_declName_287_ = lean_ctor_get(v_f_201_, 0);
lean_inc(v_declName_287_);
v___x_288_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_287_, v_a_208_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; uint8_t v___x_290_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
v___x_290_ = lean_unbox(v_a_289_);
lean_dec(v_a_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = l_Lean_mkAppRev(v_f_201_, v_rargs_202_);
lean_dec_ref(v_rargs_202_);
v___x_292_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_291_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec_ref(v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_323_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_323_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_323_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_323_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
if (lean_obj_tag(v_a_293_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_319_; 
lean_del_object(v___x_295_);
lean_dec(v_lastReduction_200_);
v_val_297_ = lean_ctor_get(v_a_293_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_319_ == 0)
{
v___x_299_ = v_a_293_;
v_isShared_300_ = v_isSharedCheck_319_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v_a_293_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_319_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Sym_shareCommonInc(v_val_297_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_n(v_a_302_, 2);
lean_dec_ref_known(v___x_301_, 1);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v_a_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_302_);
v___x_304_ = v_reuseFailAlloc_310_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = l_Lean_Expr_getAppFn(v_a_302_);
v___x_306_ = l_Lean_Expr_getAppNumArgs(v_a_302_);
v___x_307_ = lean_mk_empty_array_with_capacity(v___x_306_);
lean_dec(v___x_306_);
v___x_308_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_302_, v___x_307_);
v_lastReduction_200_ = v___x_304_;
v_f_201_ = v___x_305_;
v_rargs_202_ = v___x_308_;
goto _start;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_del_object(v___x_299_);
v_a_311_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_301_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_301_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v_a_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v_lastReduction_200_);
v___x_321_ = v___x_295_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_lastReduction_200_);
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
else
{
lean_dec(v_lastReduction_200_);
return v___x_292_;
}
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = l_Lean_mkAppRev(v_f_201_, v_rargs_202_);
lean_dec_ref(v_rargs_202_);
v___x_325_ = 0;
v___x_326_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_324_, v___x_325_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_350_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_350_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_350_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
if (lean_obj_tag(v_a_327_) == 1)
{
lean_object* v_val_331_; lean_object* v___x_332_; 
lean_del_object(v___x_329_);
v_val_331_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v_a_327_, 1);
v___x_332_ = l_Lean_Meta_Sym_shareCommonInc(v_val_331_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = l_Lean_Expr_getAppFn(v_a_333_);
v___x_335_ = l_Lean_Expr_getAppNumArgs(v_a_333_);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
lean_dec(v___x_335_);
v___x_337_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_333_, v___x_336_);
v_f_201_ = v___x_334_;
v_rargs_202_ = v___x_337_;
goto _start;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_lastReduction_200_);
v_a_339_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_332_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_332_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v___x_348_; 
lean_dec(v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_lastReduction_200_);
v___x_348_ = v___x_329_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_lastReduction_200_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_dec(v_lastReduction_200_);
return v___x_326_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref_known(v_f_201_, 2);
lean_dec_ref(v_rargs_202_);
lean_dec(v_lastReduction_200_);
v_a_351_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_288_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_288_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
case 11:
{
lean_object* v___x_359_; uint8_t v_transparency_360_; uint8_t v___x_361_; uint8_t v___x_362_; 
v___x_359_ = l_Lean_Meta_Context_config(v_a_205_);
v_transparency_360_ = lean_ctor_get_uint8(v___x_359_, 9);
lean_dec_ref(v___x_359_);
v___x_361_ = 3;
v___x_362_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v_keyedConfig_363_; uint8_t v_trackZetaDelta_364_; lean_object* v_zetaDeltaSet_365_; lean_object* v_lctx_366_; lean_object* v_localInstances_367_; lean_object* v_defEqCtx_x3f_368_; lean_object* v_synthPendingDepth_369_; lean_object* v_customCanUnfoldPredicate_x3f_370_; uint8_t v_univApprox_371_; uint8_t v_inTypeClassResolution_372_; uint8_t v_cacheInferType_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_keyedConfig_363_ = lean_ctor_get(v_a_205_, 0);
v_trackZetaDelta_364_ = lean_ctor_get_uint8(v_a_205_, sizeof(void*)*7);
v_zetaDeltaSet_365_ = lean_ctor_get(v_a_205_, 1);
v_lctx_366_ = lean_ctor_get(v_a_205_, 2);
v_localInstances_367_ = lean_ctor_get(v_a_205_, 3);
v_defEqCtx_x3f_368_ = lean_ctor_get(v_a_205_, 4);
v_synthPendingDepth_369_ = lean_ctor_get(v_a_205_, 5);
v_customCanUnfoldPredicate_x3f_370_ = lean_ctor_get(v_a_205_, 6);
v_univApprox_371_ = lean_ctor_get_uint8(v_a_205_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_372_ = lean_ctor_get_uint8(v_a_205_, sizeof(void*)*7 + 2);
v_cacheInferType_373_ = lean_ctor_get_uint8(v_a_205_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_363_);
v___x_374_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_361_, v_keyedConfig_363_);
lean_inc(v_customCanUnfoldPredicate_x3f_370_);
lean_inc(v_synthPendingDepth_369_);
lean_inc(v_defEqCtx_x3f_368_);
lean_inc_ref(v_localInstances_367_);
lean_inc_ref(v_lctx_366_);
lean_inc(v_zetaDeltaSet_365_);
v___x_375_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_zetaDeltaSet_365_);
lean_ctor_set(v___x_375_, 2, v_lctx_366_);
lean_ctor_set(v___x_375_, 3, v_localInstances_367_);
lean_ctor_set(v___x_375_, 4, v_defEqCtx_x3f_368_);
lean_ctor_set(v___x_375_, 5, v_synthPendingDepth_369_);
lean_ctor_set(v___x_375_, 6, v_customCanUnfoldPredicate_x3f_370_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*7, v_trackZetaDelta_364_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*7 + 1, v_univApprox_371_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*7 + 2, v_inTypeClassResolution_372_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*7 + 3, v_cacheInferType_373_);
v___x_376_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_f_201_, v___x_375_, v_a_206_, v_a_207_, v_a_208_);
lean_dec_ref_known(v___x_375_, 7);
v___y_211_ = v___x_376_;
goto v___jp_210_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_f_201_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
v___y_211_ = v___x_377_;
goto v___jp_210_;
}
}
default: 
{
lean_object* v___x_378_; 
lean_dec_ref(v_rargs_202_);
lean_dec_ref(v_f_201_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v_lastReduction_200_);
return v___x_378_;
}
}
v___jp_210_:
{
if (lean_obj_tag(v___y_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_252_; 
v_a_212_ = lean_ctor_get(v___y_211_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___y_211_);
if (v_isSharedCheck_252_ == 0)
{
v___x_214_ = v___y_211_;
v_isShared_215_ = v_isSharedCheck_252_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___y_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_252_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
if (lean_obj_tag(v_a_212_) == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_rargs_202_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v_lastReduction_200_);
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_lastReduction_200_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
else
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_251_; 
lean_del_object(v___x_214_);
lean_dec(v_lastReduction_200_);
v_val_219_ = lean_ctor_get(v_a_212_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_251_ == 0)
{
v___x_221_ = v_a_212_;
v_isShared_222_ = v_isSharedCheck_251_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v_a_212_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_251_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Meta_Sym_shareCommonInc(v_val_219_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_a_224_, v_rargs_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec_ref(v_rargs_202_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_n(v_a_226_, 2);
lean_dec_ref_known(v___x_225_, 1);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_a_226_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_226_);
v___x_228_ = v_reuseFailAlloc_234_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = l_Lean_Expr_getAppFn(v_a_226_);
v___x_230_ = l_Lean_Expr_getAppNumArgs(v_a_226_);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
lean_dec(v___x_230_);
v___x_232_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_226_, v___x_231_);
v_lastReduction_200_ = v___x_228_;
v_f_201_ = v___x_229_;
v_rargs_202_ = v___x_232_;
goto _start;
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_del_object(v___x_221_);
v_a_235_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_225_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_225_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_del_object(v___x_221_);
lean_dec_ref(v_rargs_202_);
v_a_243_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_223_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_223_);
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
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_rargs_202_);
lean_dec(v_lastReduction_200_);
v_a_253_ = lean_ctor_get(v___y_211_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___y_211_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___y_211_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___y_211_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lastReduction_200_ = stack[0].m_obj;
lean_object* v_f_201_ = stack[1].m_obj;
lean_object* v_rargs_202_ = stack[2].m_obj;
lean_object* v_a_203_ = stack[3].m_obj;
lean_object* v_a_204_ = stack[4].m_obj;
lean_object* v_a_205_ = stack[5].m_obj;
lean_object* v_a_206_ = stack[6].m_obj;
lean_object* v_a_207_ = stack[7].m_obj;
lean_object* v_a_208_ = stack[8].m_obj;
lean_object* v_res_379_;
v_res_379_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v_lastReduction_200_, v_f_201_, v_rargs_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_380_, lean_object* v_f_381_, lean_object* v_rargs_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v_lastReduction_380_, v_f_381_, v_rargs_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
return v_res_390_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object* v_e_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___y_400_; lean_object* v___x_409_; uint8_t v_transparency_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_409_ = l_Lean_Meta_Context_config(v_a_394_);
v_transparency_410_ = lean_ctor_get_uint8(v___x_409_, 9);
lean_dec_ref(v___x_409_);
v___x_411_ = l_Lean_Expr_getAppFn(v_e_391_);
v___x_412_ = l_Lean_Expr_getAppNumArgs(v_e_391_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_mk_empty_array_with_capacity(v___x_412_);
lean_dec(v___x_412_);
v___x_415_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_391_, v___x_414_);
v___x_416_ = 2;
v___x_417_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_410_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v_keyedConfig_418_; uint8_t v_trackZetaDelta_419_; lean_object* v_zetaDeltaSet_420_; lean_object* v_lctx_421_; lean_object* v_localInstances_422_; lean_object* v_defEqCtx_x3f_423_; lean_object* v_synthPendingDepth_424_; lean_object* v_customCanUnfoldPredicate_x3f_425_; uint8_t v_univApprox_426_; uint8_t v_inTypeClassResolution_427_; uint8_t v_cacheInferType_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_keyedConfig_418_ = lean_ctor_get(v_a_394_, 0);
v_trackZetaDelta_419_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7);
v_zetaDeltaSet_420_ = lean_ctor_get(v_a_394_, 1);
v_lctx_421_ = lean_ctor_get(v_a_394_, 2);
v_localInstances_422_ = lean_ctor_get(v_a_394_, 3);
v_defEqCtx_x3f_423_ = lean_ctor_get(v_a_394_, 4);
v_synthPendingDepth_424_ = lean_ctor_get(v_a_394_, 5);
v_customCanUnfoldPredicate_x3f_425_ = lean_ctor_get(v_a_394_, 6);
v_univApprox_426_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_427_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7 + 2);
v_cacheInferType_428_ = lean_ctor_get_uint8(v_a_394_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_418_);
v___x_429_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_416_, v_keyedConfig_418_);
lean_inc(v_customCanUnfoldPredicate_x3f_425_);
lean_inc(v_synthPendingDepth_424_);
lean_inc(v_defEqCtx_x3f_423_);
lean_inc_ref(v_localInstances_422_);
lean_inc_ref(v_lctx_421_);
lean_inc(v_zetaDeltaSet_420_);
v___x_430_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_zetaDeltaSet_420_);
lean_ctor_set(v___x_430_, 2, v_lctx_421_);
lean_ctor_set(v___x_430_, 3, v_localInstances_422_);
lean_ctor_set(v___x_430_, 4, v_defEqCtx_x3f_423_);
lean_ctor_set(v___x_430_, 5, v_synthPendingDepth_424_);
lean_ctor_set(v___x_430_, 6, v_customCanUnfoldPredicate_x3f_425_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*7, v_trackZetaDelta_419_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*7 + 1, v_univApprox_426_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*7 + 2, v_inTypeClassResolution_427_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*7 + 3, v_cacheInferType_428_);
v___x_431_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v___x_413_, v___x_411_, v___x_415_, v_a_392_, v_a_393_, v___x_430_, v_a_395_, v_a_396_, v_a_397_);
lean_dec_ref_known(v___x_430_, 7);
v___y_400_ = v___x_431_;
goto v___jp_399_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v___x_413_, v___x_411_, v___x_415_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
v___y_400_ = v___x_432_;
goto v___jp_399_;
}
v___jp_399_:
{
if (lean_obj_tag(v___y_400_) == 0)
{
return v___y_400_;
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_a_401_ = lean_ctor_get(v___y_400_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___y_400_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___y_400_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___y_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_reduceHead_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_391_ = stack[0].m_obj;
lean_object* v_a_392_ = stack[1].m_obj;
lean_object* v_a_393_ = stack[2].m_obj;
lean_object* v_a_394_ = stack[3].m_obj;
lean_object* v_a_395_ = stack[4].m_obj;
lean_object* v_a_396_ = stack[5].m_obj;
lean_object* v_a_397_ = stack[6].m_obj;
lean_object* v_res_433_;
v_res_433_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f___boxed(lean_object* v_e_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_442_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object* v_e_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
lean_inc_ref(v_e_443_);
v___x_451_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_463_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_463_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
if (lean_obj_tag(v_a_452_) == 0)
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_e_443_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_e_443_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
else
{
lean_object* v_val_459_; lean_object* v___x_461_; 
lean_dec_ref(v_e_443_);
v_val_459_ = lean_ctor_get(v_a_452_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v_a_452_, 1);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_val_459_);
v___x_461_ = v___x_454_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_val_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_e_443_);
v_a_464_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_451_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_451_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_reduceHead_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_443_ = stack[0].m_obj;
lean_object* v_a_444_ = stack[1].m_obj;
lean_object* v_a_445_ = stack[2].m_obj;
lean_object* v_a_446_ = stack[3].m_obj;
lean_object* v_a_447_ = stack[4].m_obj;
lean_object* v_a_448_ = stack[5].m_obj;
lean_object* v_a_449_ = stack[6].m_obj;
lean_object* v_res_472_;
v_res_472_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_e_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead___boxed(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_e_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_481_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
