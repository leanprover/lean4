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
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object* v_e_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_e_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(lean_object* v_declName_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = l_Lean_Environment_isProjectionFn(v_env_71_, v_declName_67_);
v___x_73_ = lean_box(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg___boxed(lean_object* v_declName_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_75_, v___y_76_);
lean_dec(v___y_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(lean_object* v_declName_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_79_, v___y_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___boxed(lean_object* v_declName_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1(v_declName_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg(lean_object* v_mvarId_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; lean_object* v_mctx_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_st_ref_get(v___y_98_);
v_mctx_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_mctx_101_);
lean_dec(v___x_100_);
v___x_102_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_101_, v_mvarId_97_);
lean_dec_ref(v_mctx_101_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg___boxed(lean_object* v_mvarId_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg(v_mvarId_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec(v_mvarId_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2(lean_object* v_mvarId_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg(v_mvarId_108_, v___y_112_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___boxed(lean_object* v_mvarId_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2(v_mvarId_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v_mvarId_117_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__3(lean_object* v_f_126_, lean_object* v_a_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___y_136_; lean_object* v___x_139_; uint8_t v_debug_140_; 
v___x_139_ = lean_st_ref_get(v___y_129_);
v_debug_140_ = lean_ctor_get_uint8(v___x_139_, sizeof(void*)*13);
lean_dec(v___x_139_);
if (v_debug_140_ == 0)
{
v___y_136_ = v___y_129_;
goto v___jp_135_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_126_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v___x_142_; 
lean_dec_ref_known(v___x_141_, 1);
v___x_142_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_dec_ref_known(v___x_142_, 1);
v___y_136_ = v___y_129_;
goto v___jp_135_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v_a_127_);
lean_dec_ref(v_f_126_);
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec_ref(v_a_127_);
lean_dec_ref(v_f_126_);
v_a_151_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_141_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_141_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
v___jp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = l_Lean_Expr_app___override(v_f_126_, v_a_127_);
v___x_138_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_137_, v___y_136_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__3___boxed(lean_object* v_f_159_, lean_object* v_a_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__3(v_f_159_, v_a_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(lean_object* v_revArgs_169_, lean_object* v_start_170_, lean_object* v_b_171_, lean_object* v_i_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_le(v_i_172_, v_start_170_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_i_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_181_ = l_Lean_instInhabitedExpr;
v___x_182_ = lean_unsigned_to_nat(1u);
v_i_183_ = lean_nat_sub(v_i_172_, v___x_182_);
lean_dec(v_i_172_);
v___x_184_ = lean_array_get_borrowed(v___x_181_, v_revArgs_169_, v_i_183_);
lean_inc(v___x_184_);
v___x_185_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__3(v_b_171_, v___x_184_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v_b_171_ = v_a_186_;
v_i_172_ = v_i_183_;
goto _start;
}
else
{
lean_dec(v_i_183_);
return v___x_185_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec(v_i_172_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_b_171_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0___boxed(lean_object* v_revArgs_189_, lean_object* v_start_190_, lean_object* v_b_191_, lean_object* v_i_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_189_, v_start_190_, v_b_191_, v_i_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v_start_190_);
lean_dec_ref(v_revArgs_189_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(lean_object* v_f_201_, lean_object* v_revArgs_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_array_get_size(v_revArgs_202_);
v___x_212_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_202_, v___x_210_, v_f_201_, v___x_211_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object* v_f_213_, lean_object* v_revArgs_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_f_213_, v_revArgs_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec_ref(v_revArgs_214_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(lean_object* v_lastReduction_223_, lean_object* v_f_224_, lean_object* v_rargs_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___y_234_; 
switch(lean_obj_tag(v_f_224_))
{
case 10:
{
lean_object* v_expr_284_; 
v_expr_284_ = lean_ctor_get(v_f_224_, 1);
lean_inc_ref(v_expr_284_);
lean_dec_ref_known(v_f_224_, 2);
v_f_224_ = v_expr_284_;
goto _start;
}
case 5:
{
lean_object* v_fn_286_; lean_object* v_arg_287_; lean_object* v___x_288_; 
v_fn_286_ = lean_ctor_get(v_f_224_, 0);
lean_inc_ref(v_fn_286_);
v_arg_287_ = lean_ctor_get(v_f_224_, 1);
lean_inc_ref(v_arg_287_);
lean_dec_ref_known(v_f_224_, 2);
v___x_288_ = lean_array_push(v_rargs_225_, v_arg_287_);
v_f_224_ = v_fn_286_;
v_rargs_225_ = v___x_288_;
goto _start;
}
case 6:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_array_get_size(v_rargs_225_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_nat_dec_eq(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v_lastReduction_223_);
v___x_293_ = l_Lean_Meta_Sym_betaRevS(v_f_224_, v_rargs_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_n(v_a_294_, 2);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_a_294_);
v___x_296_ = l_Lean_Expr_getAppFn(v_a_294_);
v___x_297_ = l_Lean_Expr_getAppNumArgs(v_a_294_);
v___x_298_ = lean_mk_empty_array_with_capacity(v___x_297_);
lean_dec(v___x_297_);
v___x_299_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_294_, v___x_298_);
v_lastReduction_223_ = v___x_295_;
v_f_224_ = v___x_296_;
v_rargs_225_ = v___x_299_;
goto _start;
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_293_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_293_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
else
{
lean_object* v___x_309_; 
lean_dec_ref_known(v_f_224_, 3);
lean_dec_ref(v_rargs_225_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v_lastReduction_223_);
return v___x_309_;
}
}
case 4:
{
lean_object* v_declName_310_; lean_object* v___x_311_; 
v_declName_310_ = lean_ctor_get(v_f_224_, 0);
lean_inc(v_declName_310_);
v___x_311_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_310_, v_a_231_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; uint8_t v___x_313_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = lean_unbox(v_a_312_);
lean_dec(v_a_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l_Lean_mkAppRev(v_f_224_, v_rargs_225_);
lean_dec_ref(v_rargs_225_);
v___x_315_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_314_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec_ref(v___x_314_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_346_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_346_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_346_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_346_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
if (lean_obj_tag(v_a_316_) == 1)
{
lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_342_; 
lean_del_object(v___x_318_);
lean_dec(v_lastReduction_223_);
v_val_320_ = lean_ctor_get(v_a_316_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_342_ == 0)
{
v___x_322_ = v_a_316_;
v_isShared_323_ = v_isSharedCheck_342_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_dec(v_a_316_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_342_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Sym_shareCommonInc(v_val_320_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_n(v_a_325_, 2);
lean_dec_ref_known(v___x_324_, 1);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v_a_325_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_325_);
v___x_327_ = v_reuseFailAlloc_333_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = l_Lean_Expr_getAppFn(v_a_325_);
v___x_329_ = l_Lean_Expr_getAppNumArgs(v_a_325_);
v___x_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
lean_dec(v___x_329_);
v___x_331_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_325_, v___x_330_);
v_lastReduction_223_ = v___x_327_;
v_f_224_ = v___x_328_;
v_rargs_225_ = v___x_331_;
goto _start;
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_del_object(v___x_322_);
v_a_334_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
else
{
lean_object* v___x_344_; 
lean_dec(v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_lastReduction_223_);
v___x_344_ = v___x_318_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_lastReduction_223_);
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
lean_dec(v_lastReduction_223_);
return v___x_315_;
}
}
else
{
lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = l_Lean_mkAppRev(v_f_224_, v_rargs_225_);
lean_dec_ref(v_rargs_225_);
v___x_348_ = 0;
v___x_349_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_347_, v___x_348_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_373_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_373_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_373_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_373_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
if (lean_obj_tag(v_a_350_) == 1)
{
lean_object* v_val_354_; lean_object* v___x_355_; 
lean_del_object(v___x_352_);
v_val_354_ = lean_ctor_get(v_a_350_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v_a_350_, 1);
v___x_355_ = l_Lean_Meta_Sym_shareCommonInc(v_val_354_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = l_Lean_Expr_getAppFn(v_a_356_);
v___x_358_ = l_Lean_Expr_getAppNumArgs(v_a_356_);
v___x_359_ = lean_mk_empty_array_with_capacity(v___x_358_);
lean_dec(v___x_358_);
v___x_360_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_356_, v___x_359_);
v_f_224_ = v___x_357_;
v_rargs_225_ = v___x_360_;
goto _start;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_lastReduction_223_);
v_a_362_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_355_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_355_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v_lastReduction_223_);
v___x_371_ = v___x_352_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_lastReduction_223_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_dec(v_lastReduction_223_);
return v___x_349_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref_known(v_f_224_, 2);
lean_dec_ref(v_rargs_225_);
lean_dec(v_lastReduction_223_);
v_a_374_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_311_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_311_);
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
case 11:
{
lean_object* v___x_382_; uint8_t v_transparency_383_; uint8_t v___x_384_; uint8_t v___x_385_; 
v___x_382_ = l_Lean_Meta_Context_config(v_a_228_);
v_transparency_383_ = lean_ctor_get_uint8(v___x_382_, 9);
lean_dec_ref(v___x_382_);
v___x_384_ = 3;
v___x_385_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v_keyedConfig_386_; uint8_t v_trackZetaDelta_387_; lean_object* v_zetaDeltaSet_388_; lean_object* v_lctx_389_; lean_object* v_localInstances_390_; lean_object* v_defEqCtx_x3f_391_; lean_object* v_synthPendingDepth_392_; lean_object* v_customCanUnfoldPredicate_x3f_393_; uint8_t v_univApprox_394_; uint8_t v_inTypeClassResolution_395_; uint8_t v_cacheInferType_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_keyedConfig_386_ = lean_ctor_get(v_a_228_, 0);
v_trackZetaDelta_387_ = lean_ctor_get_uint8(v_a_228_, sizeof(void*)*7);
v_zetaDeltaSet_388_ = lean_ctor_get(v_a_228_, 1);
v_lctx_389_ = lean_ctor_get(v_a_228_, 2);
v_localInstances_390_ = lean_ctor_get(v_a_228_, 3);
v_defEqCtx_x3f_391_ = lean_ctor_get(v_a_228_, 4);
v_synthPendingDepth_392_ = lean_ctor_get(v_a_228_, 5);
v_customCanUnfoldPredicate_x3f_393_ = lean_ctor_get(v_a_228_, 6);
v_univApprox_394_ = lean_ctor_get_uint8(v_a_228_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_395_ = lean_ctor_get_uint8(v_a_228_, sizeof(void*)*7 + 2);
v_cacheInferType_396_ = lean_ctor_get_uint8(v_a_228_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_386_);
v___x_397_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_384_, v_keyedConfig_386_);
lean_inc(v_customCanUnfoldPredicate_x3f_393_);
lean_inc(v_synthPendingDepth_392_);
lean_inc(v_defEqCtx_x3f_391_);
lean_inc_ref(v_localInstances_390_);
lean_inc_ref(v_lctx_389_);
lean_inc(v_zetaDeltaSet_388_);
v___x_398_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_zetaDeltaSet_388_);
lean_ctor_set(v___x_398_, 2, v_lctx_389_);
lean_ctor_set(v___x_398_, 3, v_localInstances_390_);
lean_ctor_set(v___x_398_, 4, v_defEqCtx_x3f_391_);
lean_ctor_set(v___x_398_, 5, v_synthPendingDepth_392_);
lean_ctor_set(v___x_398_, 6, v_customCanUnfoldPredicate_x3f_393_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*7, v_trackZetaDelta_387_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*7 + 1, v_univApprox_394_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*7 + 2, v_inTypeClassResolution_395_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*7 + 3, v_cacheInferType_396_);
v___x_399_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_f_224_, v___x_398_, v_a_229_, v_a_230_, v_a_231_);
lean_dec_ref_known(v___x_398_, 7);
v___y_234_ = v___x_399_;
goto v___jp_233_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_f_224_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
v___y_234_ = v___x_400_;
goto v___jp_233_;
}
}
case 2:
{
lean_object* v_mvarId_401_; lean_object* v___x_402_; 
v_mvarId_401_ = lean_ctor_get(v_f_224_, 0);
lean_inc(v_mvarId_401_);
lean_dec_ref_known(v_f_224_, 1);
v___x_402_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__2___redArg(v_mvarId_401_, v_a_229_);
lean_dec(v_mvarId_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_443_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_443_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_443_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_443_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
if (lean_obj_tag(v_a_403_) == 1)
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_439_; 
lean_del_object(v___x_405_);
lean_dec(v_lastReduction_223_);
v_val_407_ = lean_ctor_get(v_a_403_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_439_ == 0)
{
v___x_409_ = v_a_403_;
v_isShared_410_ = v_isSharedCheck_439_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v_a_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_439_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Sym_shareCommon(v_val_407_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Meta_Sym_betaRevS(v_a_412_, v_rargs_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_n(v_a_414_, 2);
lean_dec_ref_known(v___x_413_, 1);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v_a_414_);
v___x_416_ = v___x_409_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_414_);
v___x_416_ = v_reuseFailAlloc_422_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = l_Lean_Expr_getAppFn(v_a_414_);
v___x_418_ = l_Lean_Expr_getAppNumArgs(v_a_414_);
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_418_);
lean_dec(v___x_418_);
v___x_420_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_414_, v___x_419_);
v_lastReduction_223_ = v___x_416_;
v_f_224_ = v___x_417_;
v_rargs_225_ = v___x_420_;
goto _start;
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_del_object(v___x_409_);
v_a_423_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_413_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_413_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_del_object(v___x_409_);
lean_dec_ref(v_rargs_225_);
v_a_431_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_411_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_411_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v_a_403_);
lean_dec_ref(v_rargs_225_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_lastReduction_223_);
v___x_441_ = v___x_405_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_lastReduction_223_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_dec_ref(v_rargs_225_);
lean_dec(v_lastReduction_223_);
return v___x_402_;
}
}
default: 
{
lean_object* v___x_444_; 
lean_dec_ref(v_rargs_225_);
lean_dec_ref(v_f_224_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_lastReduction_223_);
return v___x_444_;
}
}
v___jp_233_:
{
if (lean_obj_tag(v___y_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_275_; 
v_a_235_ = lean_ctor_get(v___y_234_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___y_234_);
if (v_isSharedCheck_275_ == 0)
{
v___x_237_ = v___y_234_;
v_isShared_238_ = v_isSharedCheck_275_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___y_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_275_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
if (lean_obj_tag(v_a_235_) == 0)
{
lean_object* v___x_240_; 
lean_dec_ref(v_rargs_225_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_lastReduction_223_);
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_lastReduction_223_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_274_; 
lean_del_object(v___x_237_);
lean_dec(v_lastReduction_223_);
v_val_242_ = lean_ctor_get(v_a_235_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_274_ == 0)
{
v___x_244_ = v_a_235_;
v_isShared_245_ = v_isSharedCheck_274_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_dec(v_a_235_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_274_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_Sym_shareCommonInc(v_val_242_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_a_247_, v_rargs_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec_ref(v_rargs_225_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_n(v_a_249_, 2);
lean_dec_ref_known(v___x_248_, 1);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v_a_249_);
v___x_251_ = v___x_244_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_249_);
v___x_251_ = v_reuseFailAlloc_257_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = l_Lean_Expr_getAppFn(v_a_249_);
v___x_253_ = l_Lean_Expr_getAppNumArgs(v_a_249_);
v___x_254_ = lean_mk_empty_array_with_capacity(v___x_253_);
lean_dec(v___x_253_);
v___x_255_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_249_, v___x_254_);
v_lastReduction_223_ = v___x_251_;
v_f_224_ = v___x_252_;
v_rargs_225_ = v___x_255_;
goto _start;
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_del_object(v___x_244_);
v_a_258_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_248_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_248_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_del_object(v___x_244_);
lean_dec_ref(v_rargs_225_);
v_a_266_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_246_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_246_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_rargs_225_);
lean_dec(v_lastReduction_223_);
v_a_276_ = lean_ctor_get(v___y_234_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___y_234_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___y_234_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___y_234_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_445_, lean_object* v_f_446_, lean_object* v_rargs_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v_lastReduction_445_, v_f_446_, v_rargs_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___y_465_; lean_object* v___x_474_; uint8_t v_transparency_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; uint8_t v___x_482_; 
v___x_474_ = l_Lean_Meta_Context_config(v_a_459_);
v_transparency_475_ = lean_ctor_get_uint8(v___x_474_, 9);
lean_dec_ref(v___x_474_);
v___x_476_ = l_Lean_Expr_getAppFn(v_e_456_);
v___x_477_ = l_Lean_Expr_getAppNumArgs(v_e_456_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_477_);
lean_dec(v___x_477_);
v___x_480_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_456_, v___x_479_);
v___x_481_ = 2;
v___x_482_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_475_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v_keyedConfig_483_; uint8_t v_trackZetaDelta_484_; lean_object* v_zetaDeltaSet_485_; lean_object* v_lctx_486_; lean_object* v_localInstances_487_; lean_object* v_defEqCtx_x3f_488_; lean_object* v_synthPendingDepth_489_; lean_object* v_customCanUnfoldPredicate_x3f_490_; uint8_t v_univApprox_491_; uint8_t v_inTypeClassResolution_492_; uint8_t v_cacheInferType_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_keyedConfig_483_ = lean_ctor_get(v_a_459_, 0);
v_trackZetaDelta_484_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7);
v_zetaDeltaSet_485_ = lean_ctor_get(v_a_459_, 1);
v_lctx_486_ = lean_ctor_get(v_a_459_, 2);
v_localInstances_487_ = lean_ctor_get(v_a_459_, 3);
v_defEqCtx_x3f_488_ = lean_ctor_get(v_a_459_, 4);
v_synthPendingDepth_489_ = lean_ctor_get(v_a_459_, 5);
v_customCanUnfoldPredicate_x3f_490_ = lean_ctor_get(v_a_459_, 6);
v_univApprox_491_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_492_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7 + 2);
v_cacheInferType_493_ = lean_ctor_get_uint8(v_a_459_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_483_);
v___x_494_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_481_, v_keyedConfig_483_);
lean_inc(v_customCanUnfoldPredicate_x3f_490_);
lean_inc(v_synthPendingDepth_489_);
lean_inc(v_defEqCtx_x3f_488_);
lean_inc_ref(v_localInstances_487_);
lean_inc_ref(v_lctx_486_);
lean_inc(v_zetaDeltaSet_485_);
v___x_495_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_zetaDeltaSet_485_);
lean_ctor_set(v___x_495_, 2, v_lctx_486_);
lean_ctor_set(v___x_495_, 3, v_localInstances_487_);
lean_ctor_set(v___x_495_, 4, v_defEqCtx_x3f_488_);
lean_ctor_set(v___x_495_, 5, v_synthPendingDepth_489_);
lean_ctor_set(v___x_495_, 6, v_customCanUnfoldPredicate_x3f_490_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7, v_trackZetaDelta_484_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 1, v_univApprox_491_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 2, v_inTypeClassResolution_492_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 3, v_cacheInferType_493_);
v___x_496_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v___x_478_, v___x_476_, v___x_480_, v_a_457_, v_a_458_, v___x_495_, v_a_460_, v_a_461_, v_a_462_);
lean_dec_ref_known(v___x_495_, 7);
v___y_465_ = v___x_496_;
goto v___jp_464_;
}
else
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v___x_478_, v___x_476_, v___x_480_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
v___y_465_ = v___x_497_;
goto v___jp_464_;
}
v___jp_464_:
{
if (lean_obj_tag(v___y_465_) == 0)
{
return v___y_465_;
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_a_466_ = lean_ctor_get(v___y_465_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___y_465_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___y_465_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___y_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f___boxed(lean_object* v_e_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object* v_e_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; 
lean_inc_ref(v_e_507_);
v___x_515_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_527_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_527_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_527_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
if (lean_obj_tag(v_a_516_) == 0)
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_e_507_);
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_e_507_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_object* v_val_523_; lean_object* v___x_525_; 
lean_dec_ref(v_e_507_);
v_val_523_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_a_516_, 1);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_val_523_);
v___x_525_ = v___x_518_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_val_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_e_507_);
v_a_528_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_515_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_515_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead___boxed(lean_object* v_e_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_e_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
return v_res_544_;
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
