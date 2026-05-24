// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
// Imports: public import Lean.Meta.Sym.SymM public import Lean.Meta.WHNF
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_Environment_isProjectionFn(v_env_5_, v_declName_1_);
v___x_7_ = lean_box(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_13_, v___y_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___boxed(lean_object* v_declName_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0(v_declName_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(lean_object* v_lastReduction_31_, lean_object* v_f_32_, lean_object* v_rargs_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
switch(lean_obj_tag(v_f_32_))
{
case 10:
{
lean_object* v_expr_41_; 
v_expr_41_ = lean_ctor_get(v_f_32_, 1);
lean_inc_ref(v_expr_41_);
lean_dec_ref_known(v_f_32_, 2);
v_f_32_ = v_expr_41_;
goto _start;
}
case 5:
{
lean_object* v_fn_43_; lean_object* v_arg_44_; lean_object* v___x_45_; 
v_fn_43_ = lean_ctor_get(v_f_32_, 0);
lean_inc_ref(v_fn_43_);
v_arg_44_ = lean_ctor_get(v_f_32_, 1);
lean_inc_ref(v_arg_44_);
lean_dec_ref_known(v_f_32_, 2);
v___x_45_ = lean_array_push(v_rargs_33_, v_arg_44_);
v_f_32_ = v_fn_43_;
v_rargs_33_ = v___x_45_;
goto _start;
}
case 6:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_array_get_size(v_rargs_33_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_nat_dec_eq(v___x_47_, v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v_e_x27_50_; lean_object* v___x_51_; 
lean_dec(v_lastReduction_31_);
v_e_x27_50_ = l_Lean_Expr_betaRev(v_f_32_, v_rargs_33_, v___x_49_, v___x_49_);
lean_dec_ref(v_rargs_33_);
v___x_51_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_x27_50_, v_a_35_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc_n(v_a_52_, 2);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_a_52_);
v___x_54_ = l_Lean_Expr_getAppFn(v_a_52_);
v___x_55_ = l_Lean_Expr_getAppNumArgs(v_a_52_);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
lean_dec(v___x_55_);
v___x_57_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_52_, v___x_56_);
v_lastReduction_31_ = v___x_53_;
v_f_32_ = v___x_54_;
v_rargs_33_ = v___x_57_;
goto _start;
}
else
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v___x_51_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_51_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
lean_object* v___x_67_; 
lean_dec_ref_known(v_f_32_, 3);
lean_dec_ref(v_rargs_33_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v_lastReduction_31_);
return v___x_67_;
}
}
case 4:
{
lean_object* v_declName_68_; lean_object* v___x_69_; 
v_declName_68_ = lean_ctor_get(v_f_32_, 0);
lean_inc(v_declName_68_);
v___x_69_ = l_Lean_isProjectionFn___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go_spec__0___redArg(v_declName_68_, v_a_39_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; uint8_t v___x_71_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = lean_unbox(v_a_70_);
lean_dec(v_a_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = l_Lean_mkAppRev(v_f_32_, v_rargs_33_);
lean_dec_ref(v_rargs_33_);
v___x_73_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_72_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
lean_dec_ref(v___x_72_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_104_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_104_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
if (lean_obj_tag(v_a_74_) == 1)
{
lean_object* v_val_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_100_; 
lean_del_object(v___x_76_);
lean_dec(v_lastReduction_31_);
v_val_78_ = lean_ctor_get(v_a_74_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_a_74_);
if (v_isSharedCheck_100_ == 0)
{
v___x_80_ = v_a_74_;
v_isShared_81_ = v_isSharedCheck_100_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_val_78_);
lean_dec(v_a_74_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_100_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_78_, v_a_35_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_n(v_a_83_, 2);
lean_dec_ref_known(v___x_82_, 1);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v_a_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_83_);
v___x_85_ = v_reuseFailAlloc_91_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_86_ = l_Lean_Expr_getAppFn(v_a_83_);
v___x_87_ = l_Lean_Expr_getAppNumArgs(v_a_83_);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_83_, v___x_88_);
v_lastReduction_31_ = v___x_85_;
v_f_32_ = v___x_86_;
v_rargs_33_ = v___x_89_;
goto _start;
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_del_object(v___x_80_);
v_a_92_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_82_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_82_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
else
{
lean_object* v___x_102_; 
lean_dec(v_a_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v_lastReduction_31_);
v___x_102_ = v___x_76_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_lastReduction_31_);
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
else
{
lean_dec(v_lastReduction_31_);
return v___x_73_;
}
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; 
v___x_105_ = l_Lean_mkAppRev(v_f_32_, v_rargs_33_);
lean_dec_ref(v_rargs_33_);
v___x_106_ = 0;
v___x_107_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_105_, v___x_106_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_131_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_131_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_131_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_131_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 1)
{
lean_object* v_val_112_; lean_object* v___x_113_; 
lean_del_object(v___x_110_);
v_val_112_ = lean_ctor_get(v_a_108_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v_a_108_, 1);
v___x_113_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_112_, v_a_35_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = l_Lean_Expr_getAppFn(v_a_114_);
v___x_116_ = l_Lean_Expr_getAppNumArgs(v_a_114_);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_116_);
lean_dec(v___x_116_);
v___x_118_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_114_, v___x_117_);
v_f_32_ = v___x_115_;
v_rargs_33_ = v___x_118_;
goto _start;
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_lastReduction_31_);
v_a_120_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_113_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_113_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v___x_129_; 
lean_dec(v_a_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v_lastReduction_31_);
v___x_129_ = v___x_110_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_lastReduction_31_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_dec(v_lastReduction_31_);
return v___x_107_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref_known(v_f_32_, 2);
lean_dec_ref(v_rargs_33_);
lean_dec(v_lastReduction_31_);
v_a_132_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_69_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_69_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
case 11:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_reduceProj_x3f(v_f_32_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_172_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_172_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_172_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_172_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
if (lean_obj_tag(v_a_141_) == 0)
{
lean_object* v___x_146_; 
lean_dec_ref(v_rargs_33_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v_lastReduction_31_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_lastReduction_31_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v_val_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_171_; 
lean_del_object(v___x_143_);
lean_dec(v_lastReduction_31_);
v_val_148_ = lean_ctor_get(v_a_141_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_171_ == 0)
{
v___x_150_ = v_a_141_;
v_isShared_151_ = v_isSharedCheck_171_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_val_148_);
lean_dec(v_a_141_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_171_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = l_Lean_mkAppRev(v_val_148_, v_rargs_33_);
lean_dec_ref(v_rargs_33_);
v___x_153_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_152_, v_a_35_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc_n(v_a_154_, 2);
lean_dec_ref_known(v___x_153_, 1);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v_a_154_);
v___x_156_ = v___x_150_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_154_);
v___x_156_ = v_reuseFailAlloc_162_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = l_Lean_Expr_getAppFn(v_a_154_);
v___x_158_ = l_Lean_Expr_getAppNumArgs(v_a_154_);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_154_, v___x_159_);
v_lastReduction_31_ = v___x_156_;
v_f_32_ = v___x_157_;
v_rargs_33_ = v___x_160_;
goto _start;
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_del_object(v___x_150_);
v_a_163_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_153_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_153_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_rargs_33_);
lean_dec(v_lastReduction_31_);
return v___x_140_;
}
}
default: 
{
lean_object* v___x_173_; 
lean_dec_ref(v_rargs_33_);
lean_dec_ref(v_f_32_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_lastReduction_31_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go___boxed(lean_object* v_lastReduction_174_, lean_object* v_f_175_, lean_object* v_rargs_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v_lastReduction_174_, v_f_175_, v_rargs_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
return v_res_184_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0(void){
_start:
{
uint8_t v___x_185_; uint64_t v___x_186_; 
v___x_185_ = 2;
v___x_186_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(lean_object* v_e_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_195_; uint8_t v_foApprox_196_; uint8_t v_ctxApprox_197_; uint8_t v_quasiPatternApprox_198_; uint8_t v_constApprox_199_; uint8_t v_isDefEqStuckEx_200_; uint8_t v_unificationHints_201_; uint8_t v_proofIrrelevance_202_; uint8_t v_assignSyntheticOpaque_203_; uint8_t v_offsetCnstrs_204_; uint8_t v_etaStruct_205_; uint8_t v_univApprox_206_; uint8_t v_iota_207_; uint8_t v_beta_208_; uint8_t v_proj_209_; uint8_t v_zeta_210_; uint8_t v_zetaDelta_211_; uint8_t v_zetaUnused_212_; uint8_t v_zetaHave_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_253_; 
v___x_195_ = l_Lean_Meta_Context_config(v_a_190_);
v_foApprox_196_ = lean_ctor_get_uint8(v___x_195_, 0);
v_ctxApprox_197_ = lean_ctor_get_uint8(v___x_195_, 1);
v_quasiPatternApprox_198_ = lean_ctor_get_uint8(v___x_195_, 2);
v_constApprox_199_ = lean_ctor_get_uint8(v___x_195_, 3);
v_isDefEqStuckEx_200_ = lean_ctor_get_uint8(v___x_195_, 4);
v_unificationHints_201_ = lean_ctor_get_uint8(v___x_195_, 5);
v_proofIrrelevance_202_ = lean_ctor_get_uint8(v___x_195_, 6);
v_assignSyntheticOpaque_203_ = lean_ctor_get_uint8(v___x_195_, 7);
v_offsetCnstrs_204_ = lean_ctor_get_uint8(v___x_195_, 8);
v_etaStruct_205_ = lean_ctor_get_uint8(v___x_195_, 10);
v_univApprox_206_ = lean_ctor_get_uint8(v___x_195_, 11);
v_iota_207_ = lean_ctor_get_uint8(v___x_195_, 12);
v_beta_208_ = lean_ctor_get_uint8(v___x_195_, 13);
v_proj_209_ = lean_ctor_get_uint8(v___x_195_, 14);
v_zeta_210_ = lean_ctor_get_uint8(v___x_195_, 15);
v_zetaDelta_211_ = lean_ctor_get_uint8(v___x_195_, 16);
v_zetaUnused_212_ = lean_ctor_get_uint8(v___x_195_, 17);
v_zetaHave_213_ = lean_ctor_get_uint8(v___x_195_, 18);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_253_ == 0)
{
v___x_215_ = v___x_195_;
v_isShared_216_ = v_isSharedCheck_253_;
goto v_resetjp_214_;
}
else
{
lean_dec(v___x_195_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_253_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint8_t v_trackZetaDelta_217_; lean_object* v_zetaDeltaSet_218_; lean_object* v_lctx_219_; lean_object* v_localInstances_220_; lean_object* v_defEqCtx_x3f_221_; lean_object* v_synthPendingDepth_222_; lean_object* v_canUnfold_x3f_223_; uint8_t v_univApprox_224_; uint8_t v_inTypeClassResolution_225_; uint8_t v_cacheInferType_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v_config_231_; 
v_trackZetaDelta_217_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*7);
v_zetaDeltaSet_218_ = lean_ctor_get(v_a_190_, 1);
v_lctx_219_ = lean_ctor_get(v_a_190_, 2);
v_localInstances_220_ = lean_ctor_get(v_a_190_, 3);
v_defEqCtx_x3f_221_ = lean_ctor_get(v_a_190_, 4);
v_synthPendingDepth_222_ = lean_ctor_get(v_a_190_, 5);
v_canUnfold_x3f_223_ = lean_ctor_get(v_a_190_, 6);
v_univApprox_224_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_225_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*7 + 2);
v_cacheInferType_226_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*7 + 3);
v___x_227_ = l_Lean_Expr_getAppFn(v_e_187_);
v___x_228_ = l_Lean_Expr_getAppNumArgs(v_e_187_);
v___x_229_ = 2;
if (v_isShared_216_ == 0)
{
v_config_231_ = v___x_215_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 0, v_foApprox_196_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 1, v_ctxApprox_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 2, v_quasiPatternApprox_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 3, v_constApprox_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 4, v_isDefEqStuckEx_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 5, v_unificationHints_201_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 6, v_proofIrrelevance_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 7, v_assignSyntheticOpaque_203_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 8, v_offsetCnstrs_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 10, v_etaStruct_205_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 11, v_univApprox_206_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 12, v_iota_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 13, v_beta_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 14, v_proj_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 15, v_zeta_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 16, v_zetaDelta_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 17, v_zetaUnused_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, 18, v_zetaHave_213_);
v_config_231_ = v_reuseFailAlloc_252_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_key_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_ctor_set_uint8(v_config_231_, 9, v___x_229_);
v___x_232_ = l_Lean_Meta_Context_configKey(v_a_190_);
v___x_233_ = 3ULL;
v___x_234_ = lean_uint64_shift_right(v___x_232_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_228_);
lean_dec(v___x_228_);
v___x_237_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_187_, v___x_236_);
v___x_238_ = lean_uint64_shift_left(v___x_234_, v___x_233_);
v___x_239_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___closed__0);
v_key_240_ = lean_uint64_lor(v___x_238_, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_241_, 0, v_config_231_);
lean_ctor_set_uint64(v___x_241_, sizeof(void*)*1, v_key_240_);
lean_inc(v_canUnfold_x3f_223_);
lean_inc(v_synthPendingDepth_222_);
lean_inc(v_defEqCtx_x3f_221_);
lean_inc_ref(v_localInstances_220_);
lean_inc_ref(v_lctx_219_);
lean_inc(v_zetaDeltaSet_218_);
v___x_242_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_zetaDeltaSet_218_);
lean_ctor_set(v___x_242_, 2, v_lctx_219_);
lean_ctor_set(v___x_242_, 3, v_localInstances_220_);
lean_ctor_set(v___x_242_, 4, v_defEqCtx_x3f_221_);
lean_ctor_set(v___x_242_, 5, v_synthPendingDepth_222_);
lean_ctor_set(v___x_242_, 6, v_canUnfold_x3f_223_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7, v_trackZetaDelta_217_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7 + 1, v_univApprox_224_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7 + 2, v_inTypeClassResolution_225_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*7 + 3, v_cacheInferType_226_);
v___x_243_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce_0__Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f_go(v___x_235_, v___x_227_, v___x_237_, v_a_188_, v_a_189_, v___x_242_, v_a_191_, v_a_192_, v_a_193_);
lean_dec_ref_known(v___x_242_, 7);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
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
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f___boxed(lean_object* v_e_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object* v_e_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
lean_inc_ref(v_e_263_);
v___x_271_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead_x3f(v_e_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_283_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_283_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
if (lean_obj_tag(v_a_272_) == 0)
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v_e_263_);
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_e_263_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
lean_object* v_val_279_; lean_object* v___x_281_; 
lean_dec_ref(v_e_263_);
v_val_279_ = lean_ctor_get(v_a_272_, 0);
lean_inc(v_val_279_);
lean_dec_ref_known(v_a_272_, 1);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v_val_279_);
v___x_281_ = v___x_274_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_val_279_);
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
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_e_263_);
v_a_284_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_271_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_271_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead___boxed(lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v_e_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_300_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
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
