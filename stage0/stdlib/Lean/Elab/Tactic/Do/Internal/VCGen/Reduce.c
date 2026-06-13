// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.WHNF import Lean.Meta.Sym
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
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
lean_object* v_val_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_38_; 
v_val_13_ = lean_ctor_get(v_a_12_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v_a_12_);
if (v_isSharedCheck_38_ == 0)
{
v___x_15_ = v_a_12_;
v_isShared_16_ = v_isSharedCheck_38_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_val_13_);
lean_dec(v_a_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_38_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
uint8_t v___x_17_; 
v___x_17_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_8_, v_a_10_);
lean_dec(v_a_10_);
lean_dec_ref(v_struct_8_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
lean_dec_ref_known(v___x_11_, 1);
v___x_18_ = l_Lean_Meta_Sym_unfoldReducible(v_val_13_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_29_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_29_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_a_19_);
v___x_24_ = v___x_15_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_19_);
v___x_24_ = v_reuseFailAlloc_28_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_26_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
lean_del_object(v___x_15_);
v_a_30_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_18_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_18_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
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
lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_46_; 
lean_dec(v_a_12_);
lean_dec(v_a_10_);
lean_dec_ref(v_struct_8_);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; 
v_unused_47_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_47_);
v___x_40_ = v___x_11_;
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
else
{
lean_dec(v___x_11_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_box(0);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_42_);
v___x_44_ = v___x_40_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
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
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_dec_ref(v_struct_8_);
lean_dec(v_idx_7_);
v_a_48_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_9_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_9_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec_ref(v_e_1_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f___boxed(lean_object* v_e_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_e_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(lean_object* v_declName_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v_env_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_68_ = lean_st_ref_get(v___y_66_);
v_env_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_env_69_);
lean_dec(v___x_68_);
v___x_70_ = l_Lean_Environment_isProjectionFn(v_env_69_, v_declName_65_);
v___x_71_ = lean_box(v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(lean_object* v_declName_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_73_, v___y_74_);
lean_dec(v___y_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(lean_object* v_declName_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_77_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object* v_declName_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(v_declName_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_94_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0(void){
_start:
{
uint8_t v___x_95_; uint64_t v___x_96_; 
v___x_95_ = 3;
v___x_96_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_95_);
return v___x_96_;
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
v___x_144_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_x27_143_, v_a_101_);
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
v___x_175_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_171_, v_a_101_);
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
v___x_206_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_205_, v_a_101_);
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
lean_object* v___x_233_; uint8_t v_foApprox_234_; uint8_t v_ctxApprox_235_; uint8_t v_quasiPatternApprox_236_; uint8_t v_constApprox_237_; uint8_t v_isDefEqStuckEx_238_; uint8_t v_unificationHints_239_; uint8_t v_proofIrrelevance_240_; uint8_t v_assignSyntheticOpaque_241_; uint8_t v_offsetCnstrs_242_; uint8_t v_etaStruct_243_; uint8_t v_univApprox_244_; uint8_t v_iota_245_; uint8_t v_beta_246_; uint8_t v_proj_247_; uint8_t v_zeta_248_; uint8_t v_zetaDelta_249_; uint8_t v_zetaUnused_250_; uint8_t v_zetaHave_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_280_; 
v___x_233_ = l_Lean_Meta_Context_config(v_a_102_);
v_foApprox_234_ = lean_ctor_get_uint8(v___x_233_, 0);
v_ctxApprox_235_ = lean_ctor_get_uint8(v___x_233_, 1);
v_quasiPatternApprox_236_ = lean_ctor_get_uint8(v___x_233_, 2);
v_constApprox_237_ = lean_ctor_get_uint8(v___x_233_, 3);
v_isDefEqStuckEx_238_ = lean_ctor_get_uint8(v___x_233_, 4);
v_unificationHints_239_ = lean_ctor_get_uint8(v___x_233_, 5);
v_proofIrrelevance_240_ = lean_ctor_get_uint8(v___x_233_, 6);
v_assignSyntheticOpaque_241_ = lean_ctor_get_uint8(v___x_233_, 7);
v_offsetCnstrs_242_ = lean_ctor_get_uint8(v___x_233_, 8);
v_etaStruct_243_ = lean_ctor_get_uint8(v___x_233_, 10);
v_univApprox_244_ = lean_ctor_get_uint8(v___x_233_, 11);
v_iota_245_ = lean_ctor_get_uint8(v___x_233_, 12);
v_beta_246_ = lean_ctor_get_uint8(v___x_233_, 13);
v_proj_247_ = lean_ctor_get_uint8(v___x_233_, 14);
v_zeta_248_ = lean_ctor_get_uint8(v___x_233_, 15);
v_zetaDelta_249_ = lean_ctor_get_uint8(v___x_233_, 16);
v_zetaUnused_250_ = lean_ctor_get_uint8(v___x_233_, 17);
v_zetaHave_251_ = lean_ctor_get_uint8(v___x_233_, 18);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_280_ == 0)
{
v___x_253_ = v___x_233_;
v_isShared_254_ = v_isSharedCheck_280_;
goto v_resetjp_252_;
}
else
{
lean_dec(v___x_233_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_280_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint8_t v_trackZetaDelta_255_; lean_object* v_zetaDeltaSet_256_; lean_object* v_lctx_257_; lean_object* v_localInstances_258_; lean_object* v_defEqCtx_x3f_259_; lean_object* v_synthPendingDepth_260_; lean_object* v_canUnfold_x3f_261_; uint8_t v_univApprox_262_; uint8_t v_inTypeClassResolution_263_; uint8_t v_cacheInferType_264_; uint8_t v___x_265_; lean_object* v_config_267_; 
v_trackZetaDelta_255_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7);
v_zetaDeltaSet_256_ = lean_ctor_get(v_a_102_, 1);
v_lctx_257_ = lean_ctor_get(v_a_102_, 2);
v_localInstances_258_ = lean_ctor_get(v_a_102_, 3);
v_defEqCtx_x3f_259_ = lean_ctor_get(v_a_102_, 4);
v_synthPendingDepth_260_ = lean_ctor_get(v_a_102_, 5);
v_canUnfold_x3f_261_ = lean_ctor_get(v_a_102_, 6);
v_univApprox_262_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_263_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7 + 2);
v_cacheInferType_264_ = lean_ctor_get_uint8(v_a_102_, sizeof(void*)*7 + 3);
v___x_265_ = 3;
if (v_isShared_254_ == 0)
{
v_config_267_ = v___x_253_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 0, v_foApprox_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 1, v_ctxApprox_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 2, v_quasiPatternApprox_236_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 3, v_constApprox_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 4, v_isDefEqStuckEx_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 5, v_unificationHints_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 6, v_proofIrrelevance_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 7, v_assignSyntheticOpaque_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 8, v_offsetCnstrs_242_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 10, v_etaStruct_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 11, v_univApprox_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 12, v_iota_245_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 13, v_beta_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 14, v_proj_247_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 15, v_zeta_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 16, v_zetaDelta_249_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 17, v_zetaUnused_250_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, 18, v_zetaHave_251_);
v_config_267_ = v_reuseFailAlloc_279_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v_key_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_ctor_set_uint8(v_config_267_, 9, v___x_265_);
v___x_268_ = l_Lean_Meta_Context_configKey(v_a_102_);
v___x_269_ = 3ULL;
v___x_270_ = lean_uint64_shift_right(v___x_268_, v___x_269_);
v___x_271_ = lean_uint64_shift_left(v___x_270_, v___x_269_);
v___x_272_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___closed__0);
v_key_273_ = lean_uint64_lor(v___x_271_, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_274_, 0, v_config_267_);
lean_ctor_set_uint64(v___x_274_, sizeof(void*)*1, v_key_273_);
lean_inc(v_canUnfold_x3f_261_);
lean_inc(v_synthPendingDepth_260_);
lean_inc(v_defEqCtx_x3f_259_);
lean_inc_ref(v_localInstances_258_);
lean_inc_ref(v_lctx_257_);
lean_inc(v_zetaDeltaSet_256_);
v___x_275_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_zetaDeltaSet_256_);
lean_ctor_set(v___x_275_, 2, v_lctx_257_);
lean_ctor_set(v___x_275_, 3, v_localInstances_258_);
lean_ctor_set(v___x_275_, 4, v_defEqCtx_x3f_259_);
lean_ctor_set(v___x_275_, 5, v_synthPendingDepth_260_);
lean_ctor_set(v___x_275_, 6, v_canUnfold_x3f_261_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*7, v_trackZetaDelta_255_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*7 + 1, v_univApprox_262_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*7 + 2, v_inTypeClassResolution_263_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*7 + 3, v_cacheInferType_264_);
v___x_276_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceProjAndUnfold_x3f(v_f_98_, v___x_275_, v_a_103_, v_a_104_, v_a_105_);
lean_dec_ref_known(v___x_275_, 7);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v_a_108_ = v_a_277_;
goto v___jp_107_;
}
else
{
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_278_; 
v_a_278_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_278_);
lean_dec_ref_known(v___x_276_, 1);
v_a_108_ = v_a_278_;
goto v___jp_107_;
}
else
{
lean_dec_ref(v_rargs_99_);
lean_dec(v_lastReduction_97_);
return v___x_276_;
}
}
}
}
}
default: 
{
lean_object* v___x_281_; 
lean_dec_ref(v_rargs_99_);
lean_dec_ref(v_f_98_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v_lastReduction_97_);
return v___x_281_;
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
v___x_114_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_110_, v_a_101_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_282_, lean_object* v_f_283_, lean_object* v_rargs_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v_lastReduction_282_, v_f_283_, v_rargs_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
return v_res_292_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0(void){
_start:
{
uint8_t v___x_293_; uint64_t v___x_294_; 
v___x_293_ = 2;
v___x_294_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; uint8_t v_foApprox_304_; uint8_t v_ctxApprox_305_; uint8_t v_quasiPatternApprox_306_; uint8_t v_constApprox_307_; uint8_t v_isDefEqStuckEx_308_; uint8_t v_unificationHints_309_; uint8_t v_proofIrrelevance_310_; uint8_t v_assignSyntheticOpaque_311_; uint8_t v_offsetCnstrs_312_; uint8_t v_etaStruct_313_; uint8_t v_univApprox_314_; uint8_t v_iota_315_; uint8_t v_beta_316_; uint8_t v_proj_317_; uint8_t v_zeta_318_; uint8_t v_zetaDelta_319_; uint8_t v_zetaUnused_320_; uint8_t v_zetaHave_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_361_; 
v___x_303_ = l_Lean_Meta_Context_config(v_a_298_);
v_foApprox_304_ = lean_ctor_get_uint8(v___x_303_, 0);
v_ctxApprox_305_ = lean_ctor_get_uint8(v___x_303_, 1);
v_quasiPatternApprox_306_ = lean_ctor_get_uint8(v___x_303_, 2);
v_constApprox_307_ = lean_ctor_get_uint8(v___x_303_, 3);
v_isDefEqStuckEx_308_ = lean_ctor_get_uint8(v___x_303_, 4);
v_unificationHints_309_ = lean_ctor_get_uint8(v___x_303_, 5);
v_proofIrrelevance_310_ = lean_ctor_get_uint8(v___x_303_, 6);
v_assignSyntheticOpaque_311_ = lean_ctor_get_uint8(v___x_303_, 7);
v_offsetCnstrs_312_ = lean_ctor_get_uint8(v___x_303_, 8);
v_etaStruct_313_ = lean_ctor_get_uint8(v___x_303_, 10);
v_univApprox_314_ = lean_ctor_get_uint8(v___x_303_, 11);
v_iota_315_ = lean_ctor_get_uint8(v___x_303_, 12);
v_beta_316_ = lean_ctor_get_uint8(v___x_303_, 13);
v_proj_317_ = lean_ctor_get_uint8(v___x_303_, 14);
v_zeta_318_ = lean_ctor_get_uint8(v___x_303_, 15);
v_zetaDelta_319_ = lean_ctor_get_uint8(v___x_303_, 16);
v_zetaUnused_320_ = lean_ctor_get_uint8(v___x_303_, 17);
v_zetaHave_321_ = lean_ctor_get_uint8(v___x_303_, 18);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_361_ == 0)
{
v___x_323_ = v___x_303_;
v_isShared_324_ = v_isSharedCheck_361_;
goto v_resetjp_322_;
}
else
{
lean_dec(v___x_303_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_361_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v_trackZetaDelta_325_; lean_object* v_zetaDeltaSet_326_; lean_object* v_lctx_327_; lean_object* v_localInstances_328_; lean_object* v_defEqCtx_x3f_329_; lean_object* v_synthPendingDepth_330_; lean_object* v_canUnfold_x3f_331_; uint8_t v_univApprox_332_; uint8_t v_inTypeClassResolution_333_; uint8_t v_cacheInferType_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v_config_339_; 
v_trackZetaDelta_325_ = lean_ctor_get_uint8(v_a_298_, sizeof(void*)*7);
v_zetaDeltaSet_326_ = lean_ctor_get(v_a_298_, 1);
v_lctx_327_ = lean_ctor_get(v_a_298_, 2);
v_localInstances_328_ = lean_ctor_get(v_a_298_, 3);
v_defEqCtx_x3f_329_ = lean_ctor_get(v_a_298_, 4);
v_synthPendingDepth_330_ = lean_ctor_get(v_a_298_, 5);
v_canUnfold_x3f_331_ = lean_ctor_get(v_a_298_, 6);
v_univApprox_332_ = lean_ctor_get_uint8(v_a_298_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_333_ = lean_ctor_get_uint8(v_a_298_, sizeof(void*)*7 + 2);
v_cacheInferType_334_ = lean_ctor_get_uint8(v_a_298_, sizeof(void*)*7 + 3);
v___x_335_ = l_Lean_Expr_getAppFn(v_e_295_);
v___x_336_ = l_Lean_Expr_getAppNumArgs(v_e_295_);
v___x_337_ = 2;
if (v_isShared_324_ == 0)
{
v_config_339_ = v___x_323_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 0, v_foApprox_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 1, v_ctxApprox_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 2, v_quasiPatternApprox_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 3, v_constApprox_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 4, v_isDefEqStuckEx_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 5, v_unificationHints_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 6, v_proofIrrelevance_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 7, v_assignSyntheticOpaque_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 8, v_offsetCnstrs_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 10, v_etaStruct_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 11, v_univApprox_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 12, v_iota_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 13, v_beta_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 14, v_proj_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 15, v_zeta_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 16, v_zetaDelta_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 17, v_zetaUnused_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, 18, v_zetaHave_321_);
v_config_339_ = v_reuseFailAlloc_360_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v_key_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_ctor_set_uint8(v_config_339_, 9, v___x_337_);
v___x_340_ = l_Lean_Meta_Context_configKey(v_a_298_);
v___x_341_ = 3ULL;
v___x_342_ = lean_uint64_shift_right(v___x_340_, v___x_341_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_mk_empty_array_with_capacity(v___x_336_);
lean_dec(v___x_336_);
v___x_345_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_295_, v___x_344_);
v___x_346_ = lean_uint64_shift_left(v___x_342_, v___x_341_);
v___x_347_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0);
v_key_348_ = lean_uint64_lor(v___x_346_, v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_349_, 0, v_config_339_);
lean_ctor_set_uint64(v___x_349_, sizeof(void*)*1, v_key_348_);
lean_inc(v_canUnfold_x3f_331_);
lean_inc(v_synthPendingDepth_330_);
lean_inc(v_defEqCtx_x3f_329_);
lean_inc_ref(v_localInstances_328_);
lean_inc_ref(v_lctx_327_);
lean_inc(v_zetaDeltaSet_326_);
v___x_350_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_zetaDeltaSet_326_);
lean_ctor_set(v___x_350_, 2, v_lctx_327_);
lean_ctor_set(v___x_350_, 3, v_localInstances_328_);
lean_ctor_set(v___x_350_, 4, v_defEqCtx_x3f_329_);
lean_ctor_set(v___x_350_, 5, v_synthPendingDepth_330_);
lean_ctor_set(v___x_350_, 6, v_canUnfold_x3f_331_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*7, v_trackZetaDelta_325_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*7 + 1, v_univApprox_332_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*7 + 2, v_inTypeClassResolution_333_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*7 + 3, v_cacheInferType_334_);
v___x_351_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v___x_343_, v___x_335_, v___x_345_, v_a_296_, v_a_297_, v___x_350_, v_a_299_, v_a_300_, v_a_301_);
lean_dec_ref_known(v___x_350_, 7);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object* v_e_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
lean_inc_ref(v_e_371_);
v___x_379_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_391_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_391_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_391_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
if (lean_obj_tag(v_a_380_) == 0)
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_e_371_);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_e_371_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v_val_387_; lean_object* v___x_389_; 
lean_dec_ref(v_e_371_);
v_val_387_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v_a_380_, 1);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_val_387_);
v___x_389_ = v___x_382_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_val_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_e_371_);
v_a_392_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_379_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_379_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(lean_object* v_e_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v_e_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_408_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym(builtin);
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
lean_object* initialize_Lean_Meta_Sym(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym(builtin);
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
