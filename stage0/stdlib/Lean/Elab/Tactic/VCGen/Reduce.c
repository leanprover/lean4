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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(lean_object* v_f_97_, lean_object* v_a_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___y_107_; lean_object* v___x_110_; uint8_t v_debug_111_; 
v___x_110_ = lean_st_ref_get(v___y_100_);
v_debug_111_ = lean_ctor_get_uint8(v___x_110_, sizeof(void*)*11);
lean_dec(v___x_110_);
if (v_debug_111_ == 0)
{
v___y_107_ = v___y_100_;
goto v___jp_106_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_97_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; 
lean_dec_ref_known(v___x_112_, 1);
v___x_113_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_dec_ref_known(v___x_113_, 1);
v___y_107_ = v___y_100_;
goto v___jp_106_;
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
lean_dec_ref(v_a_98_);
lean_dec_ref(v_f_97_);
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
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
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec_ref(v_a_98_);
lean_dec_ref(v_f_97_);
v_a_122_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_112_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_112_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = l_Lean_Expr_app___override(v_f_97_, v_a_98_);
v___x_109_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_108_, v___y_107_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2___boxed(lean_object* v_f_130_, lean_object* v_a_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(v_f_130_, v_a_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(lean_object* v_revArgs_140_, lean_object* v_start_141_, lean_object* v_b_142_, lean_object* v_i_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_le(v_i_143_, v_start_141_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_i_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_152_ = l_Lean_instInhabitedExpr;
v___x_153_ = lean_unsigned_to_nat(1u);
v_i_154_ = lean_nat_sub(v_i_143_, v___x_153_);
lean_dec(v_i_143_);
v___x_155_ = lean_array_get_borrowed(v___x_152_, v_revArgs_140_, v_i_154_);
lean_inc(v___x_155_);
v___x_156_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0_spec__2(v_b_142_, v___x_155_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
v_b_142_ = v_a_157_;
v_i_143_ = v_i_154_;
goto _start;
}
else
{
lean_dec(v_i_154_);
return v___x_156_;
}
}
else
{
lean_object* v___x_159_; 
lean_dec(v_i_143_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v_b_142_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0___boxed(lean_object* v_revArgs_160_, lean_object* v_start_161_, lean_object* v_b_162_, lean_object* v_i_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_160_, v_start_161_, v_b_162_, v_i_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v_start_161_);
lean_dec_ref(v_revArgs_160_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(lean_object* v_f_172_, lean_object* v_revArgs_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_array_get_size(v_revArgs_173_);
v___x_183_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0_spec__0(v_revArgs_173_, v___x_181_, v_f_172_, v___x_182_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object* v_f_184_, lean_object* v_revArgs_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_f_184_, v_revArgs_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec_ref(v_revArgs_185_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(lean_object* v_lastReduction_194_, lean_object* v_f_195_, lean_object* v_rargs_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___y_205_; 
switch(lean_obj_tag(v_f_195_))
{
case 10:
{
lean_object* v_expr_255_; 
v_expr_255_ = lean_ctor_get(v_f_195_, 1);
lean_inc_ref(v_expr_255_);
lean_dec_ref_known(v_f_195_, 2);
v_f_195_ = v_expr_255_;
goto _start;
}
case 5:
{
lean_object* v_fn_257_; lean_object* v_arg_258_; lean_object* v___x_259_; 
v_fn_257_ = lean_ctor_get(v_f_195_, 0);
lean_inc_ref(v_fn_257_);
v_arg_258_ = lean_ctor_get(v_f_195_, 1);
lean_inc_ref(v_arg_258_);
lean_dec_ref_known(v_f_195_, 2);
v___x_259_ = lean_array_push(v_rargs_196_, v_arg_258_);
v_f_195_ = v_fn_257_;
v_rargs_196_ = v___x_259_;
goto _start;
}
case 6:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_array_get_size(v_rargs_196_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec(v_lastReduction_194_);
v___x_264_ = l_Lean_Meta_Sym_betaRevS(v_f_195_, v_rargs_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc_n(v_a_265_, 2);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v_a_265_);
v___x_267_ = l_Lean_Expr_getAppFn(v_a_265_);
v___x_268_ = l_Lean_Expr_getAppNumArgs(v_a_265_);
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_268_);
lean_dec(v___x_268_);
v___x_270_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_265_, v___x_269_);
v_lastReduction_194_ = v___x_266_;
v_f_195_ = v___x_267_;
v_rargs_196_ = v___x_270_;
goto _start;
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_264_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_264_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v___x_280_; 
lean_dec_ref_known(v_f_195_, 3);
lean_dec_ref(v_rargs_196_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_lastReduction_194_);
return v___x_280_;
}
}
case 4:
{
lean_object* v_declName_281_; lean_object* v___x_282_; 
v_declName_281_ = lean_ctor_get(v_f_195_, 0);
lean_inc(v_declName_281_);
v___x_282_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__1___redArg(v_declName_281_, v_a_202_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; uint8_t v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = lean_unbox(v_a_283_);
lean_dec(v_a_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = l_Lean_mkAppRev(v_f_195_, v_rargs_196_);
lean_dec_ref(v_rargs_196_);
v___x_286_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_285_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec_ref(v___x_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_317_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_317_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_317_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_317_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
if (lean_obj_tag(v_a_287_) == 1)
{
lean_object* v_val_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_313_; 
lean_del_object(v___x_289_);
lean_dec(v_lastReduction_194_);
v_val_291_ = lean_ctor_get(v_a_287_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_313_ == 0)
{
v___x_293_ = v_a_287_;
v_isShared_294_ = v_isSharedCheck_313_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_val_291_);
lean_dec(v_a_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_313_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Sym_shareCommonInc(v_val_291_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_n(v_a_296_, 2);
lean_dec_ref_known(v___x_295_, 1);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v_a_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_296_);
v___x_298_ = v_reuseFailAlloc_304_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = l_Lean_Expr_getAppFn(v_a_296_);
v___x_300_ = l_Lean_Expr_getAppNumArgs(v_a_296_);
v___x_301_ = lean_mk_empty_array_with_capacity(v___x_300_);
lean_dec(v___x_300_);
v___x_302_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_296_, v___x_301_);
v_lastReduction_194_ = v___x_298_;
v_f_195_ = v___x_299_;
v_rargs_196_ = v___x_302_;
goto _start;
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_del_object(v___x_293_);
v_a_305_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_295_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_295_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
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
}
else
{
lean_object* v___x_315_; 
lean_dec(v_a_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_lastReduction_194_);
v___x_315_ = v___x_289_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_lastReduction_194_);
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
else
{
lean_dec(v_lastReduction_194_);
return v___x_286_;
}
}
else
{
lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = l_Lean_mkAppRev(v_f_195_, v_rargs_196_);
lean_dec_ref(v_rargs_196_);
v___x_319_ = 0;
v___x_320_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_318_, v___x_319_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_344_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_344_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_344_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_344_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
if (lean_obj_tag(v_a_321_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_326_; 
lean_del_object(v___x_323_);
v_val_325_ = lean_ctor_get(v_a_321_, 0);
lean_inc(v_val_325_);
lean_dec_ref_known(v_a_321_, 1);
v___x_326_ = l_Lean_Meta_Sym_shareCommonInc(v_val_325_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = l_Lean_Expr_getAppFn(v_a_327_);
v___x_329_ = l_Lean_Expr_getAppNumArgs(v_a_327_);
v___x_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
lean_dec(v___x_329_);
v___x_331_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_327_, v___x_330_);
v_f_195_ = v___x_328_;
v_rargs_196_ = v___x_331_;
goto _start;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_lastReduction_194_);
v_a_333_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_326_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_326_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v___x_342_; 
lean_dec(v_a_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_lastReduction_194_);
v___x_342_ = v___x_323_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_lastReduction_194_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_dec(v_lastReduction_194_);
return v___x_320_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref_known(v_f_195_, 2);
lean_dec_ref(v_rargs_196_);
lean_dec(v_lastReduction_194_);
v_a_345_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_282_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_282_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
case 11:
{
lean_object* v___x_353_; uint8_t v_transparency_354_; uint8_t v___x_355_; uint8_t v___x_356_; 
v___x_353_ = l_Lean_Meta_Context_config(v_a_199_);
v_transparency_354_ = lean_ctor_get_uint8(v___x_353_, 9);
lean_dec_ref(v___x_353_);
v___x_355_ = 3;
v___x_356_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v_keyedConfig_357_; uint8_t v_trackZetaDelta_358_; lean_object* v_zetaDeltaSet_359_; lean_object* v_lctx_360_; lean_object* v_localInstances_361_; lean_object* v_defEqCtx_x3f_362_; lean_object* v_synthPendingDepth_363_; lean_object* v_customCanUnfoldPredicate_x3f_364_; uint8_t v_univApprox_365_; uint8_t v_inTypeClassResolution_366_; uint8_t v_cacheInferType_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_keyedConfig_357_ = lean_ctor_get(v_a_199_, 0);
v_trackZetaDelta_358_ = lean_ctor_get_uint8(v_a_199_, sizeof(void*)*7);
v_zetaDeltaSet_359_ = lean_ctor_get(v_a_199_, 1);
v_lctx_360_ = lean_ctor_get(v_a_199_, 2);
v_localInstances_361_ = lean_ctor_get(v_a_199_, 3);
v_defEqCtx_x3f_362_ = lean_ctor_get(v_a_199_, 4);
v_synthPendingDepth_363_ = lean_ctor_get(v_a_199_, 5);
v_customCanUnfoldPredicate_x3f_364_ = lean_ctor_get(v_a_199_, 6);
v_univApprox_365_ = lean_ctor_get_uint8(v_a_199_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_366_ = lean_ctor_get_uint8(v_a_199_, sizeof(void*)*7 + 2);
v_cacheInferType_367_ = lean_ctor_get_uint8(v_a_199_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_357_);
v___x_368_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_355_, v_keyedConfig_357_);
lean_inc(v_customCanUnfoldPredicate_x3f_364_);
lean_inc(v_synthPendingDepth_363_);
lean_inc(v_defEqCtx_x3f_362_);
lean_inc_ref(v_localInstances_361_);
lean_inc_ref(v_lctx_360_);
lean_inc(v_zetaDeltaSet_359_);
v___x_369_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_zetaDeltaSet_359_);
lean_ctor_set(v___x_369_, 2, v_lctx_360_);
lean_ctor_set(v___x_369_, 3, v_localInstances_361_);
lean_ctor_set(v___x_369_, 4, v_defEqCtx_x3f_362_);
lean_ctor_set(v___x_369_, 5, v_synthPendingDepth_363_);
lean_ctor_set(v___x_369_, 6, v_customCanUnfoldPredicate_x3f_364_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*7, v_trackZetaDelta_358_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*7 + 1, v_univApprox_365_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*7 + 2, v_inTypeClassResolution_366_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*7 + 3, v_cacheInferType_367_);
v___x_370_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_f_195_, v___x_369_, v_a_200_, v_a_201_, v_a_202_);
lean_dec_ref_known(v___x_369_, 7);
v___y_205_ = v___x_370_;
goto v___jp_204_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceProjAndUnfold_x3f(v_f_195_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
v___y_205_ = v___x_371_;
goto v___jp_204_;
}
}
default: 
{
lean_object* v___x_372_; 
lean_dec_ref(v_rargs_196_);
lean_dec_ref(v_f_195_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_lastReduction_194_);
return v___x_372_;
}
}
v___jp_204_:
{
if (lean_obj_tag(v___y_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_246_; 
v_a_206_ = lean_ctor_get(v___y_205_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___y_205_);
if (v_isSharedCheck_246_ == 0)
{
v___x_208_ = v___y_205_;
v_isShared_209_ = v_isSharedCheck_246_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___y_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_246_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
if (lean_obj_tag(v_a_206_) == 0)
{
lean_object* v___x_211_; 
lean_dec_ref(v_rargs_196_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v_lastReduction_194_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_lastReduction_194_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v_val_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_245_; 
lean_del_object(v___x_208_);
lean_dec(v_lastReduction_194_);
v_val_213_ = lean_ctor_get(v_a_206_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_245_ == 0)
{
v___x_215_ = v_a_206_;
v_isShared_216_ = v_isSharedCheck_245_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_val_213_);
lean_dec(v_a_206_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_245_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Sym_shareCommonInc(v_val_213_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go_spec__0(v_a_218_, v_rargs_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec_ref(v_rargs_196_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_n(v_a_220_, 2);
lean_dec_ref_known(v___x_219_, 1);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v_a_220_);
v___x_222_ = v___x_215_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_220_);
v___x_222_ = v_reuseFailAlloc_228_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = l_Lean_Expr_getAppFn(v_a_220_);
v___x_224_ = l_Lean_Expr_getAppNumArgs(v_a_220_);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
lean_dec(v___x_224_);
v___x_226_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_220_, v___x_225_);
v_lastReduction_194_ = v___x_222_;
v_f_195_ = v___x_223_;
v_rargs_196_ = v___x_226_;
goto _start;
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_del_object(v___x_215_);
v_a_229_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_219_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_219_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_del_object(v___x_215_);
lean_dec_ref(v_rargs_196_);
v_a_237_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_217_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_217_);
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
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_rargs_196_);
lean_dec(v_lastReduction_194_);
v_a_247_ = lean_ctor_get(v___y_205_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___y_205_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___y_205_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___y_205_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_373_, lean_object* v_f_374_, lean_object* v_rargs_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v_lastReduction_373_, v_f_374_, v_rargs_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___y_393_; lean_object* v___x_402_; uint8_t v_transparency_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; uint8_t v___x_410_; 
v___x_402_ = l_Lean_Meta_Context_config(v_a_387_);
v_transparency_403_ = lean_ctor_get_uint8(v___x_402_, 9);
lean_dec_ref(v___x_402_);
v___x_404_ = l_Lean_Expr_getAppFn(v_e_384_);
v___x_405_ = l_Lean_Expr_getAppNumArgs(v_e_384_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_mk_empty_array_with_capacity(v___x_405_);
lean_dec(v___x_405_);
v___x_408_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_384_, v___x_407_);
v___x_409_ = 2;
v___x_410_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_403_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v_keyedConfig_411_; uint8_t v_trackZetaDelta_412_; lean_object* v_zetaDeltaSet_413_; lean_object* v_lctx_414_; lean_object* v_localInstances_415_; lean_object* v_defEqCtx_x3f_416_; lean_object* v_synthPendingDepth_417_; lean_object* v_customCanUnfoldPredicate_x3f_418_; uint8_t v_univApprox_419_; uint8_t v_inTypeClassResolution_420_; uint8_t v_cacheInferType_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_keyedConfig_411_ = lean_ctor_get(v_a_387_, 0);
v_trackZetaDelta_412_ = lean_ctor_get_uint8(v_a_387_, sizeof(void*)*7);
v_zetaDeltaSet_413_ = lean_ctor_get(v_a_387_, 1);
v_lctx_414_ = lean_ctor_get(v_a_387_, 2);
v_localInstances_415_ = lean_ctor_get(v_a_387_, 3);
v_defEqCtx_x3f_416_ = lean_ctor_get(v_a_387_, 4);
v_synthPendingDepth_417_ = lean_ctor_get(v_a_387_, 5);
v_customCanUnfoldPredicate_x3f_418_ = lean_ctor_get(v_a_387_, 6);
v_univApprox_419_ = lean_ctor_get_uint8(v_a_387_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_420_ = lean_ctor_get_uint8(v_a_387_, sizeof(void*)*7 + 2);
v_cacheInferType_421_ = lean_ctor_get_uint8(v_a_387_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_411_);
v___x_422_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_409_, v_keyedConfig_411_);
lean_inc(v_customCanUnfoldPredicate_x3f_418_);
lean_inc(v_synthPendingDepth_417_);
lean_inc(v_defEqCtx_x3f_416_);
lean_inc_ref(v_localInstances_415_);
lean_inc_ref(v_lctx_414_);
lean_inc(v_zetaDeltaSet_413_);
v___x_423_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_zetaDeltaSet_413_);
lean_ctor_set(v___x_423_, 2, v_lctx_414_);
lean_ctor_set(v___x_423_, 3, v_localInstances_415_);
lean_ctor_set(v___x_423_, 4, v_defEqCtx_x3f_416_);
lean_ctor_set(v___x_423_, 5, v_synthPendingDepth_417_);
lean_ctor_set(v___x_423_, 6, v_customCanUnfoldPredicate_x3f_418_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*7, v_trackZetaDelta_412_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*7 + 1, v_univApprox_419_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*7 + 2, v_inTypeClassResolution_420_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*7 + 3, v_cacheInferType_421_);
v___x_424_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v___x_406_, v___x_404_, v___x_408_, v_a_385_, v_a_386_, v___x_423_, v_a_388_, v_a_389_, v_a_390_);
lean_dec_ref_known(v___x_423_, 7);
v___y_393_ = v___x_424_;
goto v___jp_392_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = l___private_Lean_Elab_Tactic_VCGen_Reduce_0__Lean_Elab_Tactic_VCGen_reduceHead_x3f_go(v___x_406_, v___x_404_, v___x_408_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
v___y_393_ = v___x_425_;
goto v___jp_392_;
}
v___jp_392_:
{
if (lean_obj_tag(v___y_393_) == 0)
{
return v___y_393_;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___y_393_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___y_393_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___y_393_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___y_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f___boxed(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; 
lean_inc_ref(v_e_435_);
v___x_443_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_455_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_455_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_455_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_455_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
if (lean_obj_tag(v_a_444_) == 0)
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_e_435_);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_e_435_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v_val_451_; lean_object* v___x_453_; 
lean_dec_ref(v_e_435_);
v_val_451_ = lean_ctor_get(v_a_444_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v_a_444_, 1);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_val_451_);
v___x_453_ = v___x_446_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_val_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v_e_435_);
v_a_456_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_443_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_443_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Elab_Tactic_VCGen_reduceHead(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_472_;
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
