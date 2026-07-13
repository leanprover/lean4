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
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0;
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
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0(void){
_start:
{
uint8_t v___x_97_; uint64_t v___x_98_; 
v___x_97_ = 3;
v___x_98_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(lean_object* v_lastReduction_99_, lean_object* v_f_100_, lean_object* v_rargs_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_a_110_; 
switch(lean_obj_tag(v_f_100_))
{
case 10:
{
lean_object* v_expr_136_; 
v_expr_136_ = lean_ctor_get(v_f_100_, 1);
lean_inc_ref(v_expr_136_);
lean_dec_ref_known(v_f_100_, 2);
v_f_100_ = v_expr_136_;
goto _start;
}
case 5:
{
lean_object* v_fn_138_; lean_object* v_arg_139_; lean_object* v___x_140_; 
v_fn_138_ = lean_ctor_get(v_f_100_, 0);
lean_inc_ref(v_fn_138_);
v_arg_139_ = lean_ctor_get(v_f_100_, 1);
lean_inc_ref(v_arg_139_);
lean_dec_ref_known(v_f_100_, 2);
v___x_140_ = lean_array_push(v_rargs_101_, v_arg_139_);
v_f_100_ = v_fn_138_;
v_rargs_101_ = v___x_140_;
goto _start;
}
case 6:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_142_ = lean_array_get_size(v_rargs_101_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_nat_dec_eq(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v_e_x27_145_; lean_object* v___x_146_; 
lean_dec(v_lastReduction_99_);
v_e_x27_145_ = l_Lean_Expr_betaRev(v_f_100_, v_rargs_101_, v___x_144_, v___x_144_);
lean_dec_ref(v_rargs_101_);
v___x_146_ = l_Lean_Meta_Sym_shareCommonInc(v_e_x27_145_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc_n(v_a_147_, 2);
lean_dec_ref_known(v___x_146_, 1);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_a_147_);
v___x_149_ = l_Lean_Expr_getAppFn(v_a_147_);
v___x_150_ = l_Lean_Expr_getAppNumArgs(v_a_147_);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
lean_dec(v___x_150_);
v___x_152_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_147_, v___x_151_);
v_lastReduction_99_ = v___x_148_;
v_f_100_ = v___x_149_;
v_rargs_101_ = v___x_152_;
goto _start;
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_146_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_146_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v___x_162_; 
lean_dec_ref_known(v_f_100_, 3);
lean_dec_ref(v_rargs_101_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v_lastReduction_99_);
return v___x_162_;
}
}
case 4:
{
lean_object* v_declName_163_; lean_object* v___x_164_; 
v_declName_163_ = lean_ctor_get(v_f_100_, 0);
lean_inc(v_declName_163_);
v___x_164_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_163_, v_a_107_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; uint8_t v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = lean_unbox(v_a_165_);
lean_dec(v_a_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l_Lean_mkAppRev(v_f_100_, v_rargs_101_);
lean_dec_ref(v_rargs_101_);
v___x_168_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_167_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec_ref(v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_199_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_199_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_199_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_199_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
if (lean_obj_tag(v_a_169_) == 1)
{
lean_object* v_val_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_195_; 
lean_del_object(v___x_171_);
lean_dec(v_lastReduction_99_);
v_val_173_ = lean_ctor_get(v_a_169_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_a_169_);
if (v_isSharedCheck_195_ == 0)
{
v___x_175_ = v_a_169_;
v_isShared_176_ = v_isSharedCheck_195_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_val_173_);
lean_dec(v_a_169_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_195_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Sym_shareCommonInc(v_val_173_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc_n(v_a_178_, 2);
lean_dec_ref_known(v___x_177_, 1);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_a_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_178_);
v___x_180_ = v_reuseFailAlloc_186_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = l_Lean_Expr_getAppFn(v_a_178_);
v___x_182_ = l_Lean_Expr_getAppNumArgs(v_a_178_);
v___x_183_ = lean_mk_empty_array_with_capacity(v___x_182_);
lean_dec(v___x_182_);
v___x_184_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_178_, v___x_183_);
v_lastReduction_99_ = v___x_180_;
v_f_100_ = v___x_181_;
v_rargs_101_ = v___x_184_;
goto _start;
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_del_object(v___x_175_);
v_a_187_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_177_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_177_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
else
{
lean_object* v___x_197_; 
lean_dec(v_a_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_lastReduction_99_);
v___x_197_ = v___x_171_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_lastReduction_99_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_dec(v_lastReduction_99_);
return v___x_168_;
}
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; 
v___x_200_ = l_Lean_mkAppRev(v_f_100_, v_rargs_101_);
lean_dec_ref(v_rargs_101_);
v___x_201_ = 0;
v___x_202_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_200_, v___x_201_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_226_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_226_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_226_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_226_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
if (lean_obj_tag(v_a_203_) == 1)
{
lean_object* v_val_207_; lean_object* v___x_208_; 
lean_del_object(v___x_205_);
v_val_207_ = lean_ctor_get(v_a_203_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_a_203_, 1);
v___x_208_ = l_Lean_Meta_Sym_shareCommonInc(v_val_207_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = l_Lean_Expr_getAppFn(v_a_209_);
v___x_211_ = l_Lean_Expr_getAppNumArgs(v_a_209_);
v___x_212_ = lean_mk_empty_array_with_capacity(v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_209_, v___x_212_);
v_f_100_ = v___x_210_;
v_rargs_101_ = v___x_213_;
goto _start;
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_lastReduction_99_);
v_a_215_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_208_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_208_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v_a_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_lastReduction_99_);
v___x_224_ = v___x_205_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_lastReduction_99_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_dec(v_lastReduction_99_);
return v___x_202_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref_known(v_f_100_, 2);
lean_dec_ref(v_rargs_101_);
lean_dec(v_lastReduction_99_);
v_a_227_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_164_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_164_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
case 11:
{
lean_object* v___x_235_; uint8_t v_foApprox_236_; uint8_t v_ctxApprox_237_; uint8_t v_quasiPatternApprox_238_; uint8_t v_constApprox_239_; uint8_t v_isDefEqStuckEx_240_; uint8_t v_unificationHints_241_; uint8_t v_proofIrrelevance_242_; uint8_t v_assignSyntheticOpaque_243_; uint8_t v_offsetCnstrs_244_; uint8_t v_etaStruct_245_; uint8_t v_univApprox_246_; uint8_t v_iota_247_; uint8_t v_beta_248_; uint8_t v_proj_249_; uint8_t v_zeta_250_; uint8_t v_zetaDelta_251_; uint8_t v_zetaUnused_252_; uint8_t v_zetaHave_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_282_; 
v___x_235_ = l_Lean_Meta_Context_config(v_a_104_);
v_foApprox_236_ = lean_ctor_get_uint8(v___x_235_, 0);
v_ctxApprox_237_ = lean_ctor_get_uint8(v___x_235_, 1);
v_quasiPatternApprox_238_ = lean_ctor_get_uint8(v___x_235_, 2);
v_constApprox_239_ = lean_ctor_get_uint8(v___x_235_, 3);
v_isDefEqStuckEx_240_ = lean_ctor_get_uint8(v___x_235_, 4);
v_unificationHints_241_ = lean_ctor_get_uint8(v___x_235_, 5);
v_proofIrrelevance_242_ = lean_ctor_get_uint8(v___x_235_, 6);
v_assignSyntheticOpaque_243_ = lean_ctor_get_uint8(v___x_235_, 7);
v_offsetCnstrs_244_ = lean_ctor_get_uint8(v___x_235_, 8);
v_etaStruct_245_ = lean_ctor_get_uint8(v___x_235_, 10);
v_univApprox_246_ = lean_ctor_get_uint8(v___x_235_, 11);
v_iota_247_ = lean_ctor_get_uint8(v___x_235_, 12);
v_beta_248_ = lean_ctor_get_uint8(v___x_235_, 13);
v_proj_249_ = lean_ctor_get_uint8(v___x_235_, 14);
v_zeta_250_ = lean_ctor_get_uint8(v___x_235_, 15);
v_zetaDelta_251_ = lean_ctor_get_uint8(v___x_235_, 16);
v_zetaUnused_252_ = lean_ctor_get_uint8(v___x_235_, 17);
v_zetaHave_253_ = lean_ctor_get_uint8(v___x_235_, 18);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_282_ == 0)
{
v___x_255_ = v___x_235_;
v_isShared_256_ = v_isSharedCheck_282_;
goto v_resetjp_254_;
}
else
{
lean_dec(v___x_235_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_282_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v_trackZetaDelta_257_; lean_object* v_zetaDeltaSet_258_; lean_object* v_lctx_259_; lean_object* v_localInstances_260_; lean_object* v_defEqCtx_x3f_261_; lean_object* v_synthPendingDepth_262_; lean_object* v_canUnfold_x3f_263_; uint8_t v_univApprox_264_; uint8_t v_inTypeClassResolution_265_; uint8_t v_cacheInferType_266_; uint8_t v___x_267_; lean_object* v_config_269_; 
v_trackZetaDelta_257_ = lean_ctor_get_uint8(v_a_104_, sizeof(void*)*7);
v_zetaDeltaSet_258_ = lean_ctor_get(v_a_104_, 1);
v_lctx_259_ = lean_ctor_get(v_a_104_, 2);
v_localInstances_260_ = lean_ctor_get(v_a_104_, 3);
v_defEqCtx_x3f_261_ = lean_ctor_get(v_a_104_, 4);
v_synthPendingDepth_262_ = lean_ctor_get(v_a_104_, 5);
v_canUnfold_x3f_263_ = lean_ctor_get(v_a_104_, 6);
v_univApprox_264_ = lean_ctor_get_uint8(v_a_104_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_265_ = lean_ctor_get_uint8(v_a_104_, sizeof(void*)*7 + 2);
v_cacheInferType_266_ = lean_ctor_get_uint8(v_a_104_, sizeof(void*)*7 + 3);
v___x_267_ = 3;
if (v_isShared_256_ == 0)
{
v_config_269_ = v___x_255_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 0, v_foApprox_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 1, v_ctxApprox_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 2, v_quasiPatternApprox_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 3, v_constApprox_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 4, v_isDefEqStuckEx_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 5, v_unificationHints_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 6, v_proofIrrelevance_242_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 7, v_assignSyntheticOpaque_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 8, v_offsetCnstrs_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 10, v_etaStruct_245_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 11, v_univApprox_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 12, v_iota_247_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 13, v_beta_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 14, v_proj_249_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 15, v_zeta_250_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 16, v_zetaDelta_251_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 17, v_zetaUnused_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_281_, 18, v_zetaHave_253_);
v_config_269_ = v_reuseFailAlloc_281_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v_key_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_ctor_set_uint8(v_config_269_, 9, v___x_267_);
v___x_270_ = l_Lean_Meta_Context_configKey(v_a_104_);
v___x_271_ = 3ULL;
v___x_272_ = lean_uint64_shift_right(v___x_270_, v___x_271_);
v___x_273_ = lean_uint64_shift_left(v___x_272_, v___x_271_);
v___x_274_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0);
v_key_275_ = lean_uint64_lor(v___x_273_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_276_, 0, v_config_269_);
lean_ctor_set_uint64(v___x_276_, sizeof(void*)*1, v_key_275_);
lean_inc(v_canUnfold_x3f_263_);
lean_inc(v_synthPendingDepth_262_);
lean_inc(v_defEqCtx_x3f_261_);
lean_inc_ref(v_localInstances_260_);
lean_inc_ref(v_lctx_259_);
lean_inc(v_zetaDeltaSet_258_);
v___x_277_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_zetaDeltaSet_258_);
lean_ctor_set(v___x_277_, 2, v_lctx_259_);
lean_ctor_set(v___x_277_, 3, v_localInstances_260_);
lean_ctor_set(v___x_277_, 4, v_defEqCtx_x3f_261_);
lean_ctor_set(v___x_277_, 5, v_synthPendingDepth_262_);
lean_ctor_set(v___x_277_, 6, v_canUnfold_x3f_263_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*7, v_trackZetaDelta_257_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*7 + 1, v_univApprox_264_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*7 + 2, v_inTypeClassResolution_265_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*7 + 3, v_cacheInferType_266_);
v___x_278_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_f_100_, v___x_277_, v_a_105_, v_a_106_, v_a_107_);
lean_dec_ref_known(v___x_277_, 7);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v_a_110_ = v_a_279_;
goto v___jp_109_;
}
else
{
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_278_, 1);
v_a_110_ = v_a_280_;
goto v___jp_109_;
}
else
{
lean_dec_ref(v_rargs_101_);
lean_dec(v_lastReduction_99_);
return v___x_278_;
}
}
}
}
}
default: 
{
lean_object* v___x_283_; 
lean_dec_ref(v_rargs_101_);
lean_dec_ref(v_f_100_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_lastReduction_99_);
return v___x_283_;
}
}
v___jp_109_:
{
if (lean_obj_tag(v_a_110_) == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_rargs_101_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v_lastReduction_99_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_lastReduction_99_);
v_val_112_ = lean_ctor_get(v_a_110_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_a_110_);
if (v_isSharedCheck_135_ == 0)
{
v___x_114_ = v_a_110_;
v_isShared_115_ = v_isSharedCheck_135_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_dec(v_a_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_135_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_Sym_shareCommonInc(v_val_112_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l_Lean_mkAppRev(v_a_117_, v_rargs_101_);
lean_dec_ref(v_rargs_101_);
lean_inc_ref(v___x_118_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_118_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_126_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = l_Lean_Expr_getAppFn(v___x_118_);
v___x_122_ = l_Lean_Expr_getAppNumArgs(v___x_118_);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
lean_dec(v___x_122_);
v___x_124_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_118_, v___x_123_);
v_lastReduction_99_ = v___x_120_;
v_f_100_ = v___x_121_;
v_rargs_101_ = v___x_124_;
goto _start;
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_del_object(v___x_114_);
lean_dec_ref(v_rargs_101_);
v_a_127_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_116_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_116_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_284_, lean_object* v_f_285_, lean_object* v_rargs_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v_lastReduction_284_, v_f_285_, v_rargs_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
return v_res_294_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0(void){
_start:
{
uint8_t v___x_295_; uint64_t v___x_296_; 
v___x_295_ = 2;
v___x_296_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object* v_e_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; uint8_t v_foApprox_306_; uint8_t v_ctxApprox_307_; uint8_t v_quasiPatternApprox_308_; uint8_t v_constApprox_309_; uint8_t v_isDefEqStuckEx_310_; uint8_t v_unificationHints_311_; uint8_t v_proofIrrelevance_312_; uint8_t v_assignSyntheticOpaque_313_; uint8_t v_offsetCnstrs_314_; uint8_t v_etaStruct_315_; uint8_t v_univApprox_316_; uint8_t v_iota_317_; uint8_t v_beta_318_; uint8_t v_proj_319_; uint8_t v_zeta_320_; uint8_t v_zetaDelta_321_; uint8_t v_zetaUnused_322_; uint8_t v_zetaHave_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_363_; 
v___x_305_ = l_Lean_Meta_Context_config(v_a_300_);
v_foApprox_306_ = lean_ctor_get_uint8(v___x_305_, 0);
v_ctxApprox_307_ = lean_ctor_get_uint8(v___x_305_, 1);
v_quasiPatternApprox_308_ = lean_ctor_get_uint8(v___x_305_, 2);
v_constApprox_309_ = lean_ctor_get_uint8(v___x_305_, 3);
v_isDefEqStuckEx_310_ = lean_ctor_get_uint8(v___x_305_, 4);
v_unificationHints_311_ = lean_ctor_get_uint8(v___x_305_, 5);
v_proofIrrelevance_312_ = lean_ctor_get_uint8(v___x_305_, 6);
v_assignSyntheticOpaque_313_ = lean_ctor_get_uint8(v___x_305_, 7);
v_offsetCnstrs_314_ = lean_ctor_get_uint8(v___x_305_, 8);
v_etaStruct_315_ = lean_ctor_get_uint8(v___x_305_, 10);
v_univApprox_316_ = lean_ctor_get_uint8(v___x_305_, 11);
v_iota_317_ = lean_ctor_get_uint8(v___x_305_, 12);
v_beta_318_ = lean_ctor_get_uint8(v___x_305_, 13);
v_proj_319_ = lean_ctor_get_uint8(v___x_305_, 14);
v_zeta_320_ = lean_ctor_get_uint8(v___x_305_, 15);
v_zetaDelta_321_ = lean_ctor_get_uint8(v___x_305_, 16);
v_zetaUnused_322_ = lean_ctor_get_uint8(v___x_305_, 17);
v_zetaHave_323_ = lean_ctor_get_uint8(v___x_305_, 18);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_363_ == 0)
{
v___x_325_ = v___x_305_;
v_isShared_326_ = v_isSharedCheck_363_;
goto v_resetjp_324_;
}
else
{
lean_dec(v___x_305_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_363_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v_trackZetaDelta_327_; lean_object* v_zetaDeltaSet_328_; lean_object* v_lctx_329_; lean_object* v_localInstances_330_; lean_object* v_defEqCtx_x3f_331_; lean_object* v_synthPendingDepth_332_; lean_object* v_canUnfold_x3f_333_; uint8_t v_univApprox_334_; uint8_t v_inTypeClassResolution_335_; uint8_t v_cacheInferType_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v_config_341_; 
v_trackZetaDelta_327_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*7);
v_zetaDeltaSet_328_ = lean_ctor_get(v_a_300_, 1);
v_lctx_329_ = lean_ctor_get(v_a_300_, 2);
v_localInstances_330_ = lean_ctor_get(v_a_300_, 3);
v_defEqCtx_x3f_331_ = lean_ctor_get(v_a_300_, 4);
v_synthPendingDepth_332_ = lean_ctor_get(v_a_300_, 5);
v_canUnfold_x3f_333_ = lean_ctor_get(v_a_300_, 6);
v_univApprox_334_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_335_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*7 + 2);
v_cacheInferType_336_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*7 + 3);
v___x_337_ = l_Lean_Expr_getAppFn(v_e_297_);
v___x_338_ = l_Lean_Expr_getAppNumArgs(v_e_297_);
v___x_339_ = 2;
if (v_isShared_326_ == 0)
{
v_config_341_ = v___x_325_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 0, v_foApprox_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 1, v_ctxApprox_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 2, v_quasiPatternApprox_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 3, v_constApprox_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 4, v_isDefEqStuckEx_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 5, v_unificationHints_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 6, v_proofIrrelevance_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 7, v_assignSyntheticOpaque_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 8, v_offsetCnstrs_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 10, v_etaStruct_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 11, v_univApprox_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 12, v_iota_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 13, v_beta_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 14, v_proj_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 15, v_zeta_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 16, v_zetaDelta_321_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 17, v_zetaUnused_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_362_, 18, v_zetaHave_323_);
v_config_341_ = v_reuseFailAlloc_362_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v_key_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
lean_ctor_set_uint8(v_config_341_, 9, v___x_339_);
v___x_342_ = l_Lean_Meta_Context_configKey(v_a_300_);
v___x_343_ = 3ULL;
v___x_344_ = lean_uint64_shift_right(v___x_342_, v___x_343_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_mk_empty_array_with_capacity(v___x_338_);
lean_dec(v___x_338_);
v___x_347_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_297_, v___x_346_);
v___x_348_ = lean_uint64_shift_left(v___x_344_, v___x_343_);
v___x_349_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0);
v_key_350_ = lean_uint64_lor(v___x_348_, v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_351_, 0, v_config_341_);
lean_ctor_set_uint64(v___x_351_, sizeof(void*)*1, v_key_350_);
lean_inc(v_canUnfold_x3f_333_);
lean_inc(v_synthPendingDepth_332_);
lean_inc(v_defEqCtx_x3f_331_);
lean_inc_ref(v_localInstances_330_);
lean_inc_ref(v_lctx_329_);
lean_inc(v_zetaDeltaSet_328_);
v___x_352_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v_zetaDeltaSet_328_);
lean_ctor_set(v___x_352_, 2, v_lctx_329_);
lean_ctor_set(v___x_352_, 3, v_localInstances_330_);
lean_ctor_set(v___x_352_, 4, v_defEqCtx_x3f_331_);
lean_ctor_set(v___x_352_, 5, v_synthPendingDepth_332_);
lean_ctor_set(v___x_352_, 6, v_canUnfold_x3f_333_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*7, v_trackZetaDelta_327_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*7 + 1, v_univApprox_334_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*7 + 2, v_inTypeClassResolution_335_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*7 + 3, v_cacheInferType_336_);
v___x_353_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v___x_345_, v___x_337_, v___x_347_, v_a_298_, v_a_299_, v___x_352_, v_a_301_, v_a_302_, v_a_303_);
lean_dec_ref_known(v___x_352_, 7);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
lean_inc_ref(v_e_373_);
v___x_381_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_393_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_393_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
if (lean_obj_tag(v_a_382_) == 0)
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_e_373_);
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_e_373_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v_val_389_; lean_object* v___x_391_; 
lean_dec_ref(v_e_373_);
v_val_389_ = lean_ctor_get(v_a_382_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v_a_382_, 1);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_val_389_);
v___x_391_ = v___x_384_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_val_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v_e_373_);
v_a_394_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_381_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_381_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(lean_object* v_e_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v_e_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_410_;
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
