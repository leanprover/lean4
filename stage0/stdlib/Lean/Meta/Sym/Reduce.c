// Lean compiler output
// Module: Lean.Meta.Sym.Reduce
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.WHNF import Lean.ProjFns
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Sym_getLetValueS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceBeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceBeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_reduceZeta_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_reduceZeta_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_reduceZeta_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceBeta_x3f(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = l_Lean_Expr_isApp(v_e_1_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec_ref(v_e_1_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
else
{
lean_object* v_f_12_; uint8_t v___x_13_; uint8_t v___x_14_; 
v_f_12_ = l_Lean_Expr_getAppFn(v_e_1_);
v___x_13_ = 0;
v___x_14_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_13_, v_f_12_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec_ref(v_f_12_);
lean_dec_ref(v_e_1_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = l_Lean_Expr_getAppNumArgs(v_e_1_);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
lean_dec(v___x_17_);
v___x_19_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1_, v___x_18_);
v___x_20_ = l_Lean_Meta_Sym_betaRevS(v_f_12_, v___x_19_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_29_ == 0)
{
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v_a_21_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_25_);
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_20_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_20_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceBeta_x3f___boxed(lean_object* v_e_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_Sym_reduceBeta_x3f(v_e_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(lean_object* v_e_47_, lean_object* v_subst_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
if (lean_obj_tag(v_e_47_) == 8)
{
lean_object* v_value_56_; lean_object* v_body_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_value_56_ = lean_ctor_get(v_e_47_, 2);
lean_inc_ref(v_value_56_);
v_body_57_ = lean_ctor_get(v_e_47_, 3);
lean_inc_ref(v_body_57_);
lean_dec_ref_known(v_e_47_, 4);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_array_get_size(v_subst_48_);
lean_inc_ref(v_subst_48_);
v___x_60_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_56_, v___x_58_, v___x_59_, v_subst_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v___x_62_ = lean_array_push(v_subst_48_, v_a_61_);
v_e_47_ = v_body_57_;
v_subst_48_ = v___x_62_;
goto _start;
}
else
{
lean_dec_ref(v_body_57_);
lean_dec_ref(v_subst_48_);
return v___x_60_;
}
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_array_get_size(v_subst_48_);
v___x_66_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_47_, v___x_64_, v___x_65_, v_subst_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go___boxed(lean_object* v_e_67_, lean_object* v_subst_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(v_e_67_, v_subst_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0_spec__1(lean_object* v_f_77_, lean_object* v_a_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___y_87_; lean_object* v___x_90_; uint8_t v_debug_91_; 
v___x_90_ = lean_st_ref_get(v___y_80_);
v_debug_91_ = lean_ctor_get_uint8(v___x_90_, sizeof(void*)*13);
lean_dec(v___x_90_);
if (v_debug_91_ == 0)
{
v___y_87_ = v___y_80_;
goto v___jp_86_;
}
else
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_77_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; 
lean_dec_ref_known(v___x_92_, 1);
v___x_93_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_dec_ref_known(v___x_93_, 1);
v___y_87_ = v___y_80_;
goto v___jp_86_;
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v_a_78_);
lean_dec_ref(v_f_77_);
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_a_78_);
lean_dec_ref(v_f_77_);
v_a_102_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_92_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = l_Lean_Expr_app___override(v_f_77_, v_a_78_);
v___x_89_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_88_, v___y_87_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_110_, lean_object* v_a_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0_spec__1(v_f_110_, v_a_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0(lean_object* v_args_120_, lean_object* v_endIdx_121_, lean_object* v_b_122_, lean_object* v_i_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_le(v_endIdx_121_, v_i_123_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = l_Lean_instInhabitedExpr;
v___x_133_ = lean_array_get_borrowed(v___x_132_, v_args_120_, v_i_123_);
lean_inc(v___x_133_);
v___x_134_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0_spec__1(v_b_122_, v___x_133_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_i_123_, v___x_136_);
lean_dec(v_i_123_);
v_b_122_ = v_a_135_;
v_i_123_ = v___x_137_;
goto _start;
}
else
{
lean_dec(v_i_123_);
return v___x_134_;
}
}
else
{
lean_object* v___x_139_; 
lean_dec(v_i_123_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_b_122_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0___boxed(lean_object* v_args_140_, lean_object* v_endIdx_141_, lean_object* v_b_142_, lean_object* v_i_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0(v_args_140_, v_endIdx_141_, v_b_142_, v_i_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v_endIdx_141_);
lean_dec_ref(v_args_140_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0(lean_object* v_f_152_, lean_object* v_args_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_args_153_);
v___x_163_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0_spec__0(v_args_153_, v___x_162_, v_f_152_, v___x_161_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0___boxed(lean_object* v_f_164_, lean_object* v_args_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0(v_f_164_, v_args_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec_ref(v_args_165_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reduceZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v_dummy_177_; 
v___x_176_ = lean_box(0);
v_dummy_177_ = l_Lean_Expr_sort___override(v___x_176_);
return v_dummy_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f(lean_object* v_e_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_f_186_; 
v_f_186_ = l_Lean_Expr_getAppFn(v_e_178_);
if (lean_obj_tag(v_f_186_) == 8)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Meta_Sym_reduceZeta_x3f___closed__0));
v___x_188_ = l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(v_f_186_, v___x_187_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_222_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_222_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_222_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_222_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_Expr_isApp(v_e_178_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec_ref(v_e_178_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_a_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v_dummy_198_; lean_object* v_nargs_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_del_object(v___x_191_);
v_dummy_198_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZeta_x3f___closed__1, &l_Lean_Meta_Sym_reduceZeta_x3f___closed__1_once, _init_l_Lean_Meta_Sym_reduceZeta_x3f___closed__1);
v_nargs_199_ = l_Lean_Expr_getAppNumArgs(v_e_178_);
lean_inc(v_nargs_199_);
v___x_200_ = lean_mk_array(v_nargs_199_, v_dummy_198_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_sub(v_nargs_199_, v___x_201_);
lean_dec(v_nargs_199_);
v___x_203_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_178_, v___x_200_, v___x_202_);
v___x_204_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0(v_a_189_, v___x_203_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec_ref(v___x_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v_a_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_a_214_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_204_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_204_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec_ref(v_e_178_);
v_a_223_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_188_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_188_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref(v_f_186_);
lean_dec_ref(v_e_178_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___boxed(lean_object* v_e_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Meta_Sym_reduceZeta_x3f(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f(lean_object* v_e_242_, lean_object* v_unfold_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Expr_getAppFn(v_e_242_);
if (lean_obj_tag(v___x_251_) == 1)
{
lean_object* v_fvarId_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_fvarId_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_n(v_fvarId_252_, 2);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = lean_apply_1(v_unfold_243_, v_fvarId_252_);
v___x_254_ = lean_unbox(v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_fvarId_252_);
lean_dec_ref(v_e_242_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Sym_getLetValueS_x3f(v_fvarId_252_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
if (lean_obj_tag(v_a_258_) == 1)
{
lean_object* v_val_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_290_; 
v_val_259_ = lean_ctor_get(v_a_258_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_a_258_);
if (v_isSharedCheck_290_ == 0)
{
v___x_261_ = v_a_258_;
v_isShared_262_ = v_isSharedCheck_290_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_val_259_);
lean_dec(v_a_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_290_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; 
v___x_263_ = l_Lean_Expr_isApp(v_e_242_);
if (v___x_263_ == 0)
{
lean_del_object(v___x_261_);
lean_dec(v_val_259_);
lean_dec_ref(v_e_242_);
return v___x_257_;
}
else
{
lean_object* v_dummy_264_; lean_object* v_nargs_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref_known(v___x_257_, 1);
v_dummy_264_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZeta_x3f___closed__1, &l_Lean_Meta_Sym_reduceZeta_x3f___closed__1_once, _init_l_Lean_Meta_Sym_reduceZeta_x3f___closed__1);
v_nargs_265_ = l_Lean_Expr_getAppNumArgs(v_e_242_);
lean_inc(v_nargs_265_);
v___x_266_ = lean_mk_array(v_nargs_265_, v_dummy_264_);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_sub(v_nargs_265_, v___x_267_);
lean_dec(v_nargs_265_);
v___x_269_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_242_, v___x_266_, v___x_268_);
v___x_270_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0(v_val_259_, v___x_269_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec_ref(v___x_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_281_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_a_271_);
v___x_276_ = v___x_261_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
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
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_del_object(v___x_261_);
v_a_282_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_270_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_270_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
else
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_a_258_);
lean_dec_ref(v_e_242_);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_257_, 0);
lean_dec(v_unused_299_);
v___x_292_ = v___x_257_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_dec(v___x_257_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_box(0);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_dec_ref(v_e_242_);
return v___x_257_;
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref(v___x_251_);
lean_dec_ref(v_unfold_243_);
lean_dec_ref(v_e_242_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f___boxed(lean_object* v_e_302_, lean_object* v_unfold_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_302_, v_unfold_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(lean_object* v_declName_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_st_ref_get(v___y_313_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_env_316_);
lean_dec(v___x_315_);
v___x_317_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_316_, v_declName_312_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_319_, v___y_320_);
lean_dec(v___y_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(lean_object* v_declName_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_323_, v___y_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___boxed(lean_object* v_declName_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(v_declName_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f(lean_object* v_e_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Expr_getAppFn(v_e_341_);
if (lean_obj_tag(v___x_349_) == 4)
{
lean_object* v_declName_350_; lean_object* v___x_351_; lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_448_; 
v_declName_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_declName_350_);
lean_dec_ref_known(v___x_349_, 2);
v___x_351_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_350_, v_a_347_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_448_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_448_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_448_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
if (lean_obj_tag(v_a_352_) == 1)
{
lean_object* v_val_356_; uint8_t v_fromClass_357_; 
v_val_356_ = lean_ctor_get(v_a_352_, 0);
lean_inc(v_val_356_);
lean_dec_ref_known(v_a_352_, 1);
v_fromClass_357_ = lean_ctor_get_uint8(v_val_356_, sizeof(void*)*3);
lean_dec(v_val_356_);
if (v_fromClass_357_ == 0)
{
lean_object* v___x_358_; 
lean_del_object(v___x_354_);
v___x_358_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_341_, v_fromClass_357_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_439_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_439_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_439_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_439_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
if (lean_obj_tag(v_a_359_) == 1)
{
lean_object* v_val_363_; lean_object* v___y_365_; lean_object* v___x_415_; uint8_t v_transparency_416_; lean_object* v___x_417_; uint8_t v___x_418_; uint8_t v___x_419_; 
lean_del_object(v___x_361_);
v_val_363_ = lean_ctor_get(v_a_359_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_a_359_, 1);
v___x_415_ = l_Lean_Meta_Context_config(v_a_344_);
v_transparency_416_ = lean_ctor_get_uint8(v___x_415_, 9);
lean_dec_ref(v___x_415_);
v___x_417_ = l_Lean_Expr_getAppFn(v_val_363_);
v___x_418_ = 2;
v___x_419_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_416_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v_keyedConfig_420_; uint8_t v_trackZetaDelta_421_; lean_object* v_zetaDeltaSet_422_; lean_object* v_lctx_423_; lean_object* v_localInstances_424_; lean_object* v_defEqCtx_x3f_425_; lean_object* v_synthPendingDepth_426_; lean_object* v_customCanUnfoldPredicate_x3f_427_; uint8_t v_univApprox_428_; uint8_t v_inTypeClassResolution_429_; uint8_t v_cacheInferType_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_keyedConfig_420_ = lean_ctor_get(v_a_344_, 0);
v_trackZetaDelta_421_ = lean_ctor_get_uint8(v_a_344_, sizeof(void*)*7);
v_zetaDeltaSet_422_ = lean_ctor_get(v_a_344_, 1);
v_lctx_423_ = lean_ctor_get(v_a_344_, 2);
v_localInstances_424_ = lean_ctor_get(v_a_344_, 3);
v_defEqCtx_x3f_425_ = lean_ctor_get(v_a_344_, 4);
v_synthPendingDepth_426_ = lean_ctor_get(v_a_344_, 5);
v_customCanUnfoldPredicate_x3f_427_ = lean_ctor_get(v_a_344_, 6);
v_univApprox_428_ = lean_ctor_get_uint8(v_a_344_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_429_ = lean_ctor_get_uint8(v_a_344_, sizeof(void*)*7 + 2);
v_cacheInferType_430_ = lean_ctor_get_uint8(v_a_344_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_420_);
v___x_431_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_418_, v_keyedConfig_420_);
lean_inc(v_customCanUnfoldPredicate_x3f_427_);
lean_inc(v_synthPendingDepth_426_);
lean_inc(v_defEqCtx_x3f_425_);
lean_inc_ref(v_localInstances_424_);
lean_inc_ref(v_lctx_423_);
lean_inc(v_zetaDeltaSet_422_);
v___x_432_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_zetaDeltaSet_422_);
lean_ctor_set(v___x_432_, 2, v_lctx_423_);
lean_ctor_set(v___x_432_, 3, v_localInstances_424_);
lean_ctor_set(v___x_432_, 4, v_defEqCtx_x3f_425_);
lean_ctor_set(v___x_432_, 5, v_synthPendingDepth_426_);
lean_ctor_set(v___x_432_, 6, v_customCanUnfoldPredicate_x3f_427_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*7, v_trackZetaDelta_421_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*7 + 1, v_univApprox_428_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*7 + 2, v_inTypeClassResolution_429_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*7 + 3, v_cacheInferType_430_);
v___x_433_ = l_Lean_Meta_reduceProj_x3f(v___x_417_, v___x_432_, v_a_345_, v_a_346_, v_a_347_);
lean_dec_ref_known(v___x_432_, 7);
v___y_365_ = v___x_433_;
goto v___jp_364_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_reduceProj_x3f(v___x_417_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
v___y_365_ = v___x_434_;
goto v___jp_364_;
}
v___jp_364_:
{
if (lean_obj_tag(v___y_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_406_; 
v_a_366_ = lean_ctor_get(v___y_365_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___y_365_);
if (v_isSharedCheck_406_ == 0)
{
v___x_368_ = v___y_365_;
v_isShared_369_ = v_isSharedCheck_406_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___y_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_406_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
if (lean_obj_tag(v_a_366_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_401_; 
lean_del_object(v___x_368_);
v_val_370_ = lean_ctor_get(v_a_366_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_366_);
if (v_isSharedCheck_401_ == 0)
{
v___x_372_ = v_a_366_;
v_isShared_373_ = v_isSharedCheck_401_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_val_370_);
lean_dec(v_a_366_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_401_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_dummy_374_; lean_object* v_nargs_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_dummy_374_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZeta_x3f___closed__1, &l_Lean_Meta_Sym_reduceZeta_x3f___closed__1_once, _init_l_Lean_Meta_Sym_reduceZeta_x3f___closed__1);
v_nargs_375_ = l_Lean_Expr_getAppNumArgs(v_val_363_);
lean_inc(v_nargs_375_);
v___x_376_ = lean_mk_array(v_nargs_375_, v_dummy_374_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_sub(v_nargs_375_, v___x_377_);
lean_dec(v_nargs_375_);
v___x_379_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_363_, v___x_376_, v___x_378_);
v___x_380_ = l_Lean_mkAppN(v_val_370_, v___x_379_);
lean_dec_ref(v___x_379_);
v___x_381_ = l_Lean_Meta_Sym_shareCommon(v___x_380_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_392_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_392_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_392_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_392_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v_a_382_);
v___x_387_ = v___x_372_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_387_);
v___x_389_ = v___x_384_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
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
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_del_object(v___x_372_);
v_a_393_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_381_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_381_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v_a_366_);
lean_dec(v_val_363_);
v___x_402_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_402_);
v___x_404_ = v___x_368_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_val_363_);
v_a_407_ = lean_ctor_get(v___y_365_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___y_365_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___y_365_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___y_365_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_dec(v_a_359_);
v___x_435_ = lean_box(0);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_435_);
v___x_437_ = v___x_361_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
return v___x_358_;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v_e_341_);
v___x_440_ = lean_box(0);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_440_);
v___x_442_ = v___x_354_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_446_; 
lean_dec(v_a_352_);
lean_dec_ref(v_e_341_);
v___x_444_ = lean_box(0);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_444_);
v___x_446_ = v___x_354_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec_ref(v___x_349_);
lean_dec_ref(v_e_341_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f___boxed(lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_460_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_512_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_512_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_512_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_512_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_471_);
v_val_473_ = lean_ctor_get(v_a_469_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_507_ == 0)
{
v___x_475_ = v_a_469_;
v_isShared_476_ = v_isSharedCheck_507_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_val_473_);
lean_dec(v_a_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_507_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Meta_Sym_foldProjs(v_val_473_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = l_Lean_Meta_Sym_shareCommonInc(v_a_478_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_a_480_);
v___x_485_ = v___x_475_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_del_object(v___x_475_);
v_a_491_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_479_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_479_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_del_object(v___x_475_);
v_a_499_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_477_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_477_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_a_469_);
v___x_508_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_508_);
v___x_510_ = v___x_471_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f___boxed(lean_object* v_e_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec_ref(v_e_513_);
return v_res_521_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
