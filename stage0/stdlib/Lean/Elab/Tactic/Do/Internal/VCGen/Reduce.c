// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.WHNF import Lean.Meta.Sym.Util
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_projectCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object* v_e_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_e_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(lean_object* v_declName_67_, lean_object* v___y_68_){
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
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(lean_object* v_declName_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_75_, v___y_76_);
lean_dec(v___y_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(lean_object* v_declName_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_79_, v___y_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object* v_declName_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(v_declName_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(lean_object* v_lastReduction_97_, lean_object* v_f_98_, lean_object* v_rargs_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_a_108_; 
switch(lean_obj_tag(v_f_98_))
{
case 10:
{
lean_object* v_expr_134_; 
v_expr_134_ = lean_ctor_get(v_f_98_, 1);
lean_inc_ref(v_expr_134_);
lean_dec_ref_known(v_f_98_, 2);
v_f_98_ = v_expr_134_;
goto _start;
}
case 5:
{
lean_object* v_fn_136_; lean_object* v_arg_137_; lean_object* v___x_138_; 
v_fn_136_ = lean_ctor_get(v_f_98_, 0);
lean_inc_ref(v_fn_136_);
v_arg_137_ = lean_ctor_get(v_f_98_, 1);
lean_inc_ref(v_arg_137_);
lean_dec_ref_known(v_f_98_, 2);
v___x_138_ = lean_array_push(v_rargs_99_, v_arg_137_);
v_f_98_ = v_fn_136_;
v_rargs_99_ = v___x_138_;
goto _start;
}
case 6:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_140_ = lean_array_get_size(v_rargs_99_);
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v_e_x27_143_; lean_object* v___x_144_; 
lean_dec(v_lastReduction_97_);
v_e_x27_143_ = l_Lean_Expr_betaRev(v_f_98_, v_rargs_99_, v___x_142_, v___x_142_);
lean_dec_ref(v_rargs_99_);
v___x_144_ = l_Lean_Meta_Sym_shareCommonInc(v_e_x27_143_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc_n(v_a_145_, 2);
lean_dec_ref_known(v___x_144_, 1);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v_a_145_);
v___x_147_ = l_Lean_Expr_getAppFn(v_a_145_);
v___x_148_ = l_Lean_Expr_getAppNumArgs(v_a_145_);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
lean_dec(v___x_148_);
v___x_150_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_145_, v___x_149_);
v_lastReduction_97_ = v___x_146_;
v_f_98_ = v___x_147_;
v_rargs_99_ = v___x_150_;
goto _start;
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_144_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_144_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v___x_160_; 
lean_dec_ref_known(v_f_98_, 3);
lean_dec_ref(v_rargs_99_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v_lastReduction_97_);
return v___x_160_;
}
}
case 4:
{
lean_object* v_declName_161_; lean_object* v___x_162_; 
v_declName_161_ = lean_ctor_get(v_f_98_, 0);
lean_inc(v_declName_161_);
v___x_162_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_161_, v_a_105_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; uint8_t v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = lean_unbox(v_a_163_);
lean_dec(v_a_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_Lean_mkAppRev(v_f_98_, v_rargs_99_);
lean_dec_ref(v_rargs_99_);
v___x_166_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_165_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
lean_dec_ref(v___x_165_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_197_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_197_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
if (lean_obj_tag(v_a_167_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_193_; 
lean_del_object(v___x_169_);
lean_dec(v_lastReduction_97_);
v_val_171_ = lean_ctor_get(v_a_167_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_193_ == 0)
{
v___x_173_ = v_a_167_;
v_isShared_174_ = v_isSharedCheck_193_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_dec(v_a_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_193_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Sym_shareCommonInc(v_val_171_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc_n(v_a_176_, 2);
lean_dec_ref_known(v___x_175_, 1);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v_a_176_);
v___x_178_ = v___x_173_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_176_);
v___x_178_ = v_reuseFailAlloc_184_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = l_Lean_Expr_getAppFn(v_a_176_);
v___x_180_ = l_Lean_Expr_getAppNumArgs(v_a_176_);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
lean_dec(v___x_180_);
v___x_182_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_176_, v___x_181_);
v_lastReduction_97_ = v___x_178_;
v_f_98_ = v___x_179_;
v_rargs_99_ = v___x_182_;
goto _start;
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_del_object(v___x_173_);
v_a_185_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_175_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_175_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_a_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v_lastReduction_97_);
v___x_195_ = v___x_169_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_lastReduction_97_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_dec(v_lastReduction_97_);
return v___x_166_;
}
}
else
{
lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_mkAppRev(v_f_98_, v_rargs_99_);
lean_dec_ref(v_rargs_99_);
v___x_199_ = 0;
v___x_200_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_198_, v___x_199_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_224_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_224_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
if (lean_obj_tag(v_a_201_) == 1)
{
lean_object* v_val_205_; lean_object* v___x_206_; 
lean_del_object(v___x_203_);
v_val_205_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v_a_201_, 1);
v___x_206_ = l_Lean_Meta_Sym_shareCommonInc(v_val_205_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = l_Lean_Expr_getAppFn(v_a_207_);
v___x_209_ = l_Lean_Expr_getAppNumArgs(v_a_207_);
v___x_210_ = lean_mk_empty_array_with_capacity(v___x_209_);
lean_dec(v___x_209_);
v___x_211_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_207_, v___x_210_);
v_f_98_ = v___x_208_;
v_rargs_99_ = v___x_211_;
goto _start;
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_lastReduction_97_);
v_a_213_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_206_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_206_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v___x_222_; 
lean_dec(v_a_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v_lastReduction_97_);
v___x_222_ = v___x_203_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_lastReduction_97_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_dec(v_lastReduction_97_);
return v___x_200_;
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref_known(v_f_98_, 2);
lean_dec_ref(v_rargs_99_);
lean_dec(v_lastReduction_97_);
v_a_225_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_162_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_162_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
case 11:
{
lean_object* v_keyedConfig_233_; uint8_t v_trackZetaDelta_234_; lean_object* v_zetaDeltaSet_235_; lean_object* v_lctx_236_; lean_object* v_localInstances_237_; lean_object* v_defEqCtx_x3f_238_; lean_object* v_synthPendingDepth_239_; lean_object* v_customCanUnfoldPredicate_x3f_240_; uint8_t v_univApprox_241_; uint8_t v_inTypeClassResolution_242_; uint8_t v_cacheInferType_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_keyedConfig_233_ = lean_ctor_get(v_a_102_, 0);
v_trackZetaDelta_234_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7);
v_zetaDeltaSet_235_ = lean_ctor_get(v_a_102_, 1);
v_lctx_236_ = lean_ctor_get(v_a_102_, 2);
v_localInstances_237_ = lean_ctor_get(v_a_102_, 3);
v_defEqCtx_x3f_238_ = lean_ctor_get(v_a_102_, 4);
v_synthPendingDepth_239_ = lean_ctor_get(v_a_102_, 5);
v_customCanUnfoldPredicate_x3f_240_ = lean_ctor_get(v_a_102_, 6);
v_univApprox_241_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_242_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7 + 2);
v_cacheInferType_243_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7 + 3);
v___x_244_ = 3;
lean_inc_ref(v_keyedConfig_233_);
v___x_245_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_244_, v_keyedConfig_233_);
lean_inc(v_customCanUnfoldPredicate_x3f_240_);
lean_inc(v_synthPendingDepth_239_);
lean_inc(v_defEqCtx_x3f_238_);
lean_inc_ref(v_localInstances_237_);
lean_inc_ref(v_lctx_236_);
lean_inc(v_zetaDeltaSet_235_);
v___x_246_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_zetaDeltaSet_235_);
lean_ctor_set(v___x_246_, 2, v_lctx_236_);
lean_ctor_set(v___x_246_, 3, v_localInstances_237_);
lean_ctor_set(v___x_246_, 4, v_defEqCtx_x3f_238_);
lean_ctor_set(v___x_246_, 5, v_synthPendingDepth_239_);
lean_ctor_set(v___x_246_, 6, v_customCanUnfoldPredicate_x3f_240_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*7, v_trackZetaDelta_234_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*7 + 1, v_univApprox_241_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*7 + 2, v_inTypeClassResolution_242_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*7 + 3, v_cacheInferType_243_);
v___x_247_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_f_98_, v___x_246_, v_a_103_, v_a_104_, v_a_105_);
lean_dec_ref_known(v___x_246_, 7);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v_a_108_ = v_a_248_;
goto v___jp_107_;
}
else
{
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_247_, 1);
v_a_108_ = v_a_249_;
goto v___jp_107_;
}
else
{
lean_dec_ref(v_rargs_99_);
lean_dec(v_lastReduction_97_);
return v___x_247_;
}
}
}
default: 
{
lean_object* v___x_250_; 
lean_dec_ref(v_rargs_99_);
lean_dec_ref(v_f_98_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_lastReduction_97_);
return v___x_250_;
}
}
v___jp_107_:
{
if (lean_obj_tag(v_a_108_) == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v_rargs_99_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v_lastReduction_97_);
return v___x_109_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_133_; 
lean_dec(v_lastReduction_97_);
v_val_110_ = lean_ctor_get(v_a_108_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_a_108_);
if (v_isSharedCheck_133_ == 0)
{
v___x_112_ = v_a_108_;
v_isShared_113_ = v_isSharedCheck_133_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_dec(v_a_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_133_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Sym_shareCommonInc(v_val_110_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = l_Lean_mkAppRev(v_a_115_, v_rargs_99_);
lean_dec_ref(v_rargs_99_);
lean_inc_ref(v___x_116_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_116_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_124_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = l_Lean_Expr_getAppFn(v___x_116_);
v___x_120_ = l_Lean_Expr_getAppNumArgs(v___x_116_);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
lean_dec(v___x_120_);
v___x_122_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_116_, v___x_121_);
v_lastReduction_97_ = v___x_118_;
v_f_98_ = v___x_119_;
v_rargs_99_ = v___x_122_;
goto _start;
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_del_object(v___x_112_);
lean_dec_ref(v_rargs_99_);
v_a_125_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_114_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_114_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_251_, lean_object* v_f_252_, lean_object* v_rargs_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v_lastReduction_251_, v_f_252_, v_rargs_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_keyedConfig_270_; uint8_t v_trackZetaDelta_271_; lean_object* v_zetaDeltaSet_272_; lean_object* v_lctx_273_; lean_object* v_localInstances_274_; lean_object* v_defEqCtx_x3f_275_; lean_object* v_synthPendingDepth_276_; lean_object* v_customCanUnfoldPredicate_x3f_277_; uint8_t v_univApprox_278_; uint8_t v_inTypeClassResolution_279_; uint8_t v_cacheInferType_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_keyedConfig_270_ = lean_ctor_get(v_a_265_, 0);
v_trackZetaDelta_271_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*7);
v_zetaDeltaSet_272_ = lean_ctor_get(v_a_265_, 1);
v_lctx_273_ = lean_ctor_get(v_a_265_, 2);
v_localInstances_274_ = lean_ctor_get(v_a_265_, 3);
v_defEqCtx_x3f_275_ = lean_ctor_get(v_a_265_, 4);
v_synthPendingDepth_276_ = lean_ctor_get(v_a_265_, 5);
v_customCanUnfoldPredicate_x3f_277_ = lean_ctor_get(v_a_265_, 6);
v_univApprox_278_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_279_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*7 + 2);
v_cacheInferType_280_ = lean_ctor_get_uint8(v_a_265_, sizeof(void*)*7 + 3);
v___x_281_ = l_Lean_Expr_getAppFn(v_e_262_);
v___x_282_ = l_Lean_Expr_getAppNumArgs(v_e_262_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_mk_empty_array_with_capacity(v___x_282_);
lean_dec(v___x_282_);
v___x_285_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_262_, v___x_284_);
v___x_286_ = 2;
lean_inc_ref(v_keyedConfig_270_);
v___x_287_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_286_, v_keyedConfig_270_);
lean_inc(v_customCanUnfoldPredicate_x3f_277_);
lean_inc(v_synthPendingDepth_276_);
lean_inc(v_defEqCtx_x3f_275_);
lean_inc_ref(v_localInstances_274_);
lean_inc_ref(v_lctx_273_);
lean_inc(v_zetaDeltaSet_272_);
v___x_288_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_zetaDeltaSet_272_);
lean_ctor_set(v___x_288_, 2, v_lctx_273_);
lean_ctor_set(v___x_288_, 3, v_localInstances_274_);
lean_ctor_set(v___x_288_, 4, v_defEqCtx_x3f_275_);
lean_ctor_set(v___x_288_, 5, v_synthPendingDepth_276_);
lean_ctor_set(v___x_288_, 6, v_customCanUnfoldPredicate_x3f_277_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*7, v_trackZetaDelta_271_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*7 + 1, v_univApprox_278_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*7 + 2, v_inTypeClassResolution_279_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*7 + 3, v_cacheInferType_280_);
v___x_289_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v___x_283_, v___x_281_, v___x_285_, v_a_263_, v_a_264_, v___x_288_, v_a_266_, v_a_267_, v_a_268_);
lean_dec_ref_known(v___x_288_, 7);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object* v_e_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
lean_inc_ref(v_e_307_);
v___x_315_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_327_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_327_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
if (lean_obj_tag(v_a_316_) == 0)
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_e_307_);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_e_307_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v_val_323_; lean_object* v___x_325_; 
lean_dec_ref(v_e_307_);
v_val_323_ = lean_ctor_get(v_a_316_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v_a_316_, 1);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_val_323_);
v___x_325_ = v___x_318_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_val_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_e_307_);
v_a_328_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_315_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_315_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v_e_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_344_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin) {
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
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
