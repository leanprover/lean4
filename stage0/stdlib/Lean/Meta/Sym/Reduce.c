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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
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
v_debug_91_ = lean_ctor_get_uint8(v___x_90_, sizeof(void*)*12);
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
v___x_257_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_252_, v_a_246_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_304_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_304_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_304_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_304_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___x_262_; lean_object* v___x_263_; 
v___x_262_ = 0;
v___x_263_ = l_Lean_LocalDecl_value_x3f(v_a_258_, v___x_262_);
lean_dec(v_a_258_);
if (lean_obj_tag(v___x_263_) == 1)
{
lean_object* v_val_264_; uint8_t v___x_265_; 
v_val_264_ = lean_ctor_get(v___x_263_, 0);
v___x_265_ = l_Lean_Expr_isApp(v_e_242_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
lean_dec_ref(v_e_242_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_263_);
v___x_267_ = v___x_260_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_263_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_298_; 
lean_inc(v_val_264_);
lean_del_object(v___x_260_);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_299_);
v___x_270_ = v___x_263_;
v_isShared_271_ = v_isSharedCheck_298_;
goto v_resetjp_269_;
}
else
{
lean_dec(v___x_263_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_298_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_dummy_272_; lean_object* v_nargs_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_dummy_272_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZeta_x3f___closed__1, &l_Lean_Meta_Sym_reduceZeta_x3f___closed__1_once, _init_l_Lean_Meta_Sym_reduceZeta_x3f___closed__1);
v_nargs_273_ = l_Lean_Expr_getAppNumArgs(v_e_242_);
lean_inc(v_nargs_273_);
v___x_274_ = lean_mk_array(v_nargs_273_, v_dummy_272_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_sub(v_nargs_273_, v___x_275_);
lean_dec(v_nargs_273_);
v___x_277_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_242_, v___x_274_, v___x_276_);
v___x_278_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZeta_x3f_spec__0(v_val_264_, v___x_277_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec_ref(v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_289_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v_a_279_);
v___x_284_ = v___x_270_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_del_object(v___x_270_);
v_a_290_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_278_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_278_);
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
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec(v___x_263_);
lean_dec_ref(v_e_242_);
v___x_300_ = lean_box(0);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_300_);
v___x_302_ = v___x_260_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v_e_242_);
v_a_305_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_257_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_257_);
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
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v___x_251_);
lean_dec_ref(v_unfold_243_);
lean_dec_ref(v_e_242_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f___boxed(lean_object* v_e_315_, lean_object* v_unfold_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_315_, v_unfold_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(lean_object* v_declName_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; lean_object* v_env_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_st_ref_get(v___y_326_);
v_env_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_env_329_);
lean_dec(v___x_328_);
v___x_330_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_329_, v_declName_325_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_332_, v___y_333_);
lean_dec(v___y_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(lean_object* v_declName_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_336_, v___y_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___boxed(lean_object* v_declName_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(v_declName_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f(lean_object* v_e_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Expr_getAppFn(v_e_354_);
if (lean_obj_tag(v___x_362_) == 4)
{
lean_object* v_declName_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_461_; 
v_declName_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_declName_363_);
lean_dec_ref_known(v___x_362_, 2);
v___x_364_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_363_, v_a_360_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_461_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_461_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_461_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
if (lean_obj_tag(v_a_365_) == 1)
{
lean_object* v_val_369_; uint8_t v_fromClass_370_; 
v_val_369_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v_a_365_, 1);
v_fromClass_370_ = lean_ctor_get_uint8(v_val_369_, sizeof(void*)*3);
lean_dec(v_val_369_);
if (v_fromClass_370_ == 0)
{
lean_object* v___x_371_; 
lean_del_object(v___x_367_);
v___x_371_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_354_, v_fromClass_370_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_452_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_452_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_452_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_452_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
if (lean_obj_tag(v_a_372_) == 1)
{
lean_object* v_val_376_; lean_object* v___y_378_; lean_object* v___x_428_; uint8_t v_transparency_429_; lean_object* v___x_430_; uint8_t v___x_431_; uint8_t v___x_432_; 
lean_del_object(v___x_374_);
v_val_376_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_a_372_, 1);
v___x_428_ = l_Lean_Meta_Context_config(v_a_357_);
v_transparency_429_ = lean_ctor_get_uint8(v___x_428_, 9);
lean_dec_ref(v___x_428_);
v___x_430_ = l_Lean_Expr_getAppFn(v_val_376_);
v___x_431_ = 2;
v___x_432_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_429_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v_keyedConfig_433_; uint8_t v_trackZetaDelta_434_; lean_object* v_zetaDeltaSet_435_; lean_object* v_lctx_436_; lean_object* v_localInstances_437_; lean_object* v_defEqCtx_x3f_438_; lean_object* v_synthPendingDepth_439_; lean_object* v_customCanUnfoldPredicate_x3f_440_; uint8_t v_univApprox_441_; uint8_t v_inTypeClassResolution_442_; uint8_t v_cacheInferType_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_keyedConfig_433_ = lean_ctor_get(v_a_357_, 0);
v_trackZetaDelta_434_ = lean_ctor_get_uint8(v_a_357_, sizeof(void*)*7);
v_zetaDeltaSet_435_ = lean_ctor_get(v_a_357_, 1);
v_lctx_436_ = lean_ctor_get(v_a_357_, 2);
v_localInstances_437_ = lean_ctor_get(v_a_357_, 3);
v_defEqCtx_x3f_438_ = lean_ctor_get(v_a_357_, 4);
v_synthPendingDepth_439_ = lean_ctor_get(v_a_357_, 5);
v_customCanUnfoldPredicate_x3f_440_ = lean_ctor_get(v_a_357_, 6);
v_univApprox_441_ = lean_ctor_get_uint8(v_a_357_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_442_ = lean_ctor_get_uint8(v_a_357_, sizeof(void*)*7 + 2);
v_cacheInferType_443_ = lean_ctor_get_uint8(v_a_357_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_433_);
v___x_444_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_431_, v_keyedConfig_433_);
lean_inc(v_customCanUnfoldPredicate_x3f_440_);
lean_inc(v_synthPendingDepth_439_);
lean_inc(v_defEqCtx_x3f_438_);
lean_inc_ref(v_localInstances_437_);
lean_inc_ref(v_lctx_436_);
lean_inc(v_zetaDeltaSet_435_);
v___x_445_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_zetaDeltaSet_435_);
lean_ctor_set(v___x_445_, 2, v_lctx_436_);
lean_ctor_set(v___x_445_, 3, v_localInstances_437_);
lean_ctor_set(v___x_445_, 4, v_defEqCtx_x3f_438_);
lean_ctor_set(v___x_445_, 5, v_synthPendingDepth_439_);
lean_ctor_set(v___x_445_, 6, v_customCanUnfoldPredicate_x3f_440_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7, v_trackZetaDelta_434_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7 + 1, v_univApprox_441_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7 + 2, v_inTypeClassResolution_442_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*7 + 3, v_cacheInferType_443_);
v___x_446_ = l_Lean_Meta_reduceProj_x3f(v___x_430_, v___x_445_, v_a_358_, v_a_359_, v_a_360_);
lean_dec_ref_known(v___x_445_, 7);
v___y_378_ = v___x_446_;
goto v___jp_377_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_reduceProj_x3f(v___x_430_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
v___y_378_ = v___x_447_;
goto v___jp_377_;
}
v___jp_377_:
{
if (lean_obj_tag(v___y_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_419_; 
v_a_379_ = lean_ctor_get(v___y_378_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___y_378_);
if (v_isSharedCheck_419_ == 0)
{
v___x_381_ = v___y_378_;
v_isShared_382_ = v_isSharedCheck_419_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___y_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_419_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
if (lean_obj_tag(v_a_379_) == 1)
{
lean_object* v_val_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_381_);
v_val_383_ = lean_ctor_get(v_a_379_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_379_);
if (v_isSharedCheck_414_ == 0)
{
v___x_385_ = v_a_379_;
v_isShared_386_ = v_isSharedCheck_414_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_val_383_);
lean_dec(v_a_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_414_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_dummy_387_; lean_object* v_nargs_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_dummy_387_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZeta_x3f___closed__1, &l_Lean_Meta_Sym_reduceZeta_x3f___closed__1_once, _init_l_Lean_Meta_Sym_reduceZeta_x3f___closed__1);
v_nargs_388_ = l_Lean_Expr_getAppNumArgs(v_val_376_);
lean_inc(v_nargs_388_);
v___x_389_ = lean_mk_array(v_nargs_388_, v_dummy_387_);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_sub(v_nargs_388_, v___x_390_);
lean_dec(v_nargs_388_);
v___x_392_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_376_, v___x_389_, v___x_391_);
v___x_393_ = l_Lean_mkAppN(v_val_383_, v___x_392_);
lean_dec_ref(v___x_392_);
v___x_394_ = l_Lean_Meta_Sym_shareCommon(v___x_393_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_405_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_a_395_);
v___x_400_ = v___x_385_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_404_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_del_object(v___x_385_);
v_a_406_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_394_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_394_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec(v_a_379_);
lean_dec(v_val_376_);
v___x_415_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_415_);
v___x_417_ = v___x_381_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_val_376_);
v_a_420_ = lean_ctor_get(v___y_378_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___y_378_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___y_378_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___y_378_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_450_; 
lean_dec(v_a_372_);
v___x_448_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_448_);
v___x_450_ = v___x_374_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
return v___x_371_;
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec_ref(v_e_354_);
v___x_453_ = lean_box(0);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_453_);
v___x_455_ = v___x_367_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_a_365_);
lean_dec_ref(v_e_354_);
v___x_457_ = lean_box(0);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_457_);
v___x_459_ = v___x_367_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v___x_362_);
lean_dec_ref(v_e_354_);
v___x_462_ = lean_box(0);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_473_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_525_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_525_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_525_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_525_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
if (lean_obj_tag(v_a_482_) == 1)
{
lean_object* v_val_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_520_; 
lean_del_object(v___x_484_);
v_val_486_ = lean_ctor_get(v_a_482_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_482_);
if (v_isSharedCheck_520_ == 0)
{
v___x_488_ = v_a_482_;
v_isShared_489_ = v_isSharedCheck_520_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_val_486_);
lean_dec(v_a_482_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_520_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Sym_foldProjs(v_val_486_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = l_Lean_Meta_Sym_shareCommonInc(v_a_491_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_503_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_503_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_503_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_503_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v_a_493_);
v___x_498_ = v___x_488_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_498_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_del_object(v___x_488_);
v_a_504_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_492_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_492_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_del_object(v___x_488_);
v_a_512_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_490_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_490_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec(v_a_482_);
v___x_521_ = lean_box(0);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_521_);
v___x_523_ = v___x_484_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f___boxed(lean_object* v_e_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec_ref(v_e_526_);
return v_res_534_;
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
