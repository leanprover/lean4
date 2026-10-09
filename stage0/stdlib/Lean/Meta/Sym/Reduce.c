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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_Sym_reduceZeta_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_reduceZeta_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0;
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
lean_object* l_Lean_Meta_Sym_reduceBeta_x3f(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_reduceBeta_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_Meta_Sym_reduceBeta_x3f(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceBeta_x3f___boxed(lean_object* v_e_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_Sym_reduceBeta_x3f(v_e_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
return v_res_47_;
}
}
lean_object* l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(lean_object* v_e_48_, lean_object* v_subst_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
if (lean_obj_tag(v_e_48_) == 8)
{
lean_object* v_value_57_; lean_object* v_body_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_value_57_ = lean_ctor_get(v_e_48_, 2);
lean_inc_ref(v_value_57_);
v_body_58_ = lean_ctor_get(v_e_48_, 3);
lean_inc_ref(v_body_58_);
lean_dec_ref_known(v_e_48_, 4);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_array_get_size(v_subst_49_);
lean_inc_ref(v_subst_49_);
v___x_61_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_value_57_, v___x_59_, v___x_60_, v_subst_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_61_, 1);
v___x_63_ = lean_array_push(v_subst_49_, v_a_62_);
v_e_48_ = v_body_58_;
v_subst_49_ = v___x_63_;
goto _start;
}
else
{
lean_dec_ref(v_body_58_);
lean_dec_ref(v_subst_49_);
return v___x_61_;
}
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_array_get_size(v_subst_49_);
v___x_67_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_48_, v___x_65_, v___x_66_, v_subst_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_67_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_48_ = stack[0].m_obj;
lean_object* v_subst_49_ = stack[1].m_obj;
lean_object* v_a_50_ = stack[2].m_obj;
lean_object* v_a_51_ = stack[3].m_obj;
lean_object* v_a_52_ = stack[4].m_obj;
lean_object* v_a_53_ = stack[5].m_obj;
lean_object* v_a_54_ = stack[6].m_obj;
lean_object* v_a_55_ = stack[7].m_obj;
lean_object* v_res_68_;
v_res_68_ = l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(v_e_48_, v_subst_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go___boxed(lean_object* v_e_69_, lean_object* v_subst_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(v_e_69_, v_subst_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_78_;
}
}
lean_object* l_Lean_Meta_Sym_reduceZeta_x3f(lean_object* v_e_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
if (lean_obj_tag(v_e_81_) == 8)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Meta_Sym_reduceZeta_x3f___closed__0));
v___x_90_ = l___private_Lean_Meta_Sym_Reduce_0__Lean_Meta_Sym_reduceZeta_x3f_go(v_e_81_, v___x_89_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_99_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_99_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_a_91_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_95_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_a_100_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_90_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_90_);
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
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec_ref(v_e_81_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reduceZeta_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_81_ = stack[0].m_obj;
lean_object* v_a_82_ = stack[1].m_obj;
lean_object* v_a_83_ = stack[2].m_obj;
lean_object* v_a_84_ = stack[3].m_obj;
lean_object* v_a_85_ = stack[4].m_obj;
lean_object* v_a_86_ = stack[5].m_obj;
lean_object* v_a_87_ = stack[6].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Meta_Sym_reduceZeta_x3f(v_e_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZeta_x3f___boxed(lean_object* v_e_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_Sym_reduceZeta_x3f(v_e_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_119_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1(lean_object* v_f_120_, lean_object* v_a_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___y_130_; lean_object* v___x_133_; uint8_t v_debug_134_; 
v___x_133_ = lean_st_ref_get(v___y_123_);
v_debug_134_ = lean_ctor_get_uint8(v___x_133_, sizeof(void*)*12);
lean_dec(v___x_133_);
if (v_debug_134_ == 0)
{
v___y_130_ = v___y_123_;
goto v___jp_129_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_120_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_136_; 
lean_dec_ref_known(v___x_135_, 1);
v___x_136_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_dec_ref_known(v___x_136_, 1);
v___y_130_ = v___y_123_;
goto v___jp_129_;
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v_a_121_);
lean_dec_ref(v_f_120_);
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_a_121_);
lean_dec_ref(v_f_120_);
v_a_145_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_135_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = l_Lean_Expr_app___override(v_f_120_, v_a_121_);
v___x_132_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_131_, v___y_130_);
return v___x_132_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_120_ = stack[0].m_obj;
lean_object* v_a_121_ = stack[1].m_obj;
lean_object* v___y_122_ = stack[2].m_obj;
lean_object* v___y_123_ = stack[3].m_obj;
lean_object* v___y_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v___y_127_ = stack[7].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1(v_f_120_, v_a_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_154_, lean_object* v_a_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1(v_f_154_, v_a_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_163_;
}
}
lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0(lean_object* v_args_164_, lean_object* v_endIdx_165_, lean_object* v_b_166_, lean_object* v_i_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_le(v_endIdx_165_, v_i_167_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = l_Lean_instInhabitedExpr;
v___x_177_ = lean_array_get_borrowed(v___x_176_, v_args_164_, v_i_167_);
lean_inc(v___x_177_);
v___x_178_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_spec__1(v_b_166_, v___x_177_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_167_, v___x_180_);
lean_dec(v_i_167_);
v_b_166_ = v_a_179_;
v_i_167_ = v___x_181_;
goto _start;
}
else
{
lean_dec(v_i_167_);
return v___x_178_;
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v_i_167_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v_b_166_);
return v___x_183_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_164_ = stack[0].m_obj;
lean_object* v_endIdx_165_ = stack[1].m_obj;
lean_object* v_b_166_ = stack[2].m_obj;
lean_object* v_i_167_ = stack[3].m_obj;
lean_object* v___y_168_ = stack[4].m_obj;
lean_object* v___y_169_ = stack[5].m_obj;
lean_object* v___y_170_ = stack[6].m_obj;
lean_object* v___y_171_ = stack[7].m_obj;
lean_object* v___y_172_ = stack[8].m_obj;
lean_object* v___y_173_ = stack[9].m_obj;
lean_object* v_res_184_;
v_res_184_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0(v_args_164_, v_endIdx_165_, v_b_166_, v_i_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0___boxed(lean_object* v_args_185_, lean_object* v_endIdx_186_, lean_object* v_b_187_, lean_object* v_i_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0(v_args_185_, v_endIdx_186_, v_b_187_, v_i_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v_endIdx_186_);
lean_dec_ref(v_args_185_);
return v_res_196_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0(lean_object* v_f_197_, lean_object* v_args_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_array_get_size(v_args_198_);
v___x_208_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_spec__0(v_args_198_, v___x_207_, v_f_197_, v___x_206_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_197_ = stack[0].m_obj;
lean_object* v_args_198_ = stack[1].m_obj;
lean_object* v___y_199_ = stack[2].m_obj;
lean_object* v___y_200_ = stack[3].m_obj;
lean_object* v___y_201_ = stack[4].m_obj;
lean_object* v___y_202_ = stack[5].m_obj;
lean_object* v___y_203_ = stack[6].m_obj;
lean_object* v___y_204_ = stack[7].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0(v_f_197_, v_args_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0___boxed(lean_object* v_f_210_, lean_object* v_args_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0(v_f_210_, v_args_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v_args_211_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0(void){
_start:
{
lean_object* v___x_220_; lean_object* v_dummy_221_; 
v___x_220_ = lean_box(0);
v_dummy_221_ = l_Lean_Expr_sort___override(v___x_220_);
return v_dummy_221_;
}
}
lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f(lean_object* v_e_222_, lean_object* v_unfold_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Expr_getAppFn(v_e_222_);
if (lean_obj_tag(v___x_231_) == 1)
{
lean_object* v_fvarId_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_fvarId_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_n(v_fvarId_232_, 2);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = lean_apply_1(v_unfold_223_, v_fvarId_232_);
v___x_234_ = lean_unbox(v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v_fvarId_232_);
lean_dec_ref(v_e_222_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_232_, v_a_226_, v_a_228_, v_a_229_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_284_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_284_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_284_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_284_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; lean_object* v___x_243_; 
v___x_242_ = 0;
v___x_243_ = l_Lean_LocalDecl_value_x3f(v_a_238_, v___x_242_);
lean_dec(v_a_238_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; uint8_t v___x_245_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
v___x_245_ = l_Lean_Expr_isApp(v_e_222_);
if (v___x_245_ == 0)
{
lean_object* v___x_247_; 
lean_dec_ref(v_e_222_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_243_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
else
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_278_; 
lean_inc(v_val_244_);
lean_del_object(v___x_240_);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v___x_243_, 0);
lean_dec(v_unused_279_);
v___x_250_ = v___x_243_;
v_isShared_251_ = v_isSharedCheck_278_;
goto v_resetjp_249_;
}
else
{
lean_dec(v___x_243_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_278_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_dummy_252_; lean_object* v_nargs_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_dummy_252_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0, &l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0_once, _init_l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0);
v_nargs_253_ = l_Lean_Expr_getAppNumArgs(v_e_222_);
lean_inc(v_nargs_253_);
v___x_254_ = lean_mk_array(v_nargs_253_, v_dummy_252_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_sub(v_nargs_253_, v___x_255_);
lean_dec(v_nargs_253_);
v___x_257_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_222_, v___x_254_, v___x_256_);
v___x_258_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Meta_Sym_reduceZetaDelta_x3f_spec__0(v_val_244_, v___x_257_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec_ref(v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v_a_259_);
v___x_264_ = v___x_250_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_del_object(v___x_250_);
v_a_270_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_258_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_258_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_282_; 
lean_dec(v___x_243_);
lean_dec_ref(v_e_222_);
v___x_280_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_280_);
v___x_282_ = v___x_240_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec_ref(v_e_222_);
v_a_285_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_237_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_237_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v___x_231_);
lean_dec_ref(v_unfold_223_);
lean_dec_ref(v_e_222_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reduceZetaDelta_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_222_ = stack[0].m_obj;
lean_object* v_unfold_223_ = stack[1].m_obj;
lean_object* v_a_224_ = stack[2].m_obj;
lean_object* v_a_225_ = stack[3].m_obj;
lean_object* v_a_226_ = stack[4].m_obj;
lean_object* v_a_227_ = stack[5].m_obj;
lean_object* v_a_228_ = stack[6].m_obj;
lean_object* v_a_229_ = stack[7].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_222_, v_unfold_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceZetaDelta_x3f___boxed(lean_object* v_e_296_, lean_object* v_unfold_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Sym_reduceZetaDelta_x3f(v_e_296_, v_unfold_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_305_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(lean_object* v_declName_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_env_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_env_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref(v_env_310_);
lean_dec(v___x_309_);
v___x_311_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_310_, v_declName_306_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_306_ = stack[0].m_obj;
lean_object* v___y_307_ = stack[1].m_obj;
lean_object* v_res_313_;
v_res_313_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_306_, v___y_307_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg___boxed(lean_object* v_declName_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_314_, v___y_315_);
lean_dec(v___y_315_);
return v_res_317_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(lean_object* v_declName_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_318_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_318_ = stack[0].m_obj;
lean_object* v___y_319_ = stack[1].m_obj;
lean_object* v___y_320_ = stack[2].m_obj;
lean_object* v___y_321_ = stack[3].m_obj;
lean_object* v___y_322_ = stack[4].m_obj;
lean_object* v___y_323_ = stack[5].m_obj;
lean_object* v___y_324_ = stack[6].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(v_declName_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___boxed(lean_object* v_declName_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0(v_declName_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_336_;
}
}
lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f(lean_object* v_e_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Expr_getAppFn(v_e_337_);
if (lean_obj_tag(v___x_345_) == 4)
{
lean_object* v_declName_346_; lean_object* v___x_347_; lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_444_; 
v_declName_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_declName_346_);
lean_dec_ref_known(v___x_345_, 2);
v___x_347_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_reduceProjApp_x3f_spec__0___redArg(v_declName_346_, v_a_343_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_444_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_444_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_444_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
if (lean_obj_tag(v_a_348_) == 1)
{
lean_object* v_val_352_; uint8_t v_fromClass_353_; 
v_val_352_ = lean_ctor_get(v_a_348_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v_a_348_, 1);
v_fromClass_353_ = lean_ctor_get_uint8(v_val_352_, sizeof(void*)*3);
lean_dec(v_val_352_);
if (v_fromClass_353_ == 0)
{
lean_object* v___x_354_; 
lean_del_object(v___x_350_);
v___x_354_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_337_, v_fromClass_353_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_435_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_435_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_435_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_435_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
if (lean_obj_tag(v_a_355_) == 1)
{
lean_object* v_val_359_; lean_object* v___y_361_; lean_object* v___x_411_; uint8_t v_transparency_412_; lean_object* v___x_413_; uint8_t v___x_414_; uint8_t v___x_415_; 
lean_del_object(v___x_357_);
v_val_359_ = lean_ctor_get(v_a_355_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v_a_355_, 1);
v___x_411_ = l_Lean_Meta_Context_config(v_a_340_);
v_transparency_412_ = lean_ctor_get_uint8(v___x_411_, 9);
lean_dec_ref(v___x_411_);
v___x_413_ = l_Lean_Expr_getAppFn(v_val_359_);
v___x_414_ = 2;
v___x_415_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_412_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v_keyedConfig_416_; uint8_t v_trackZetaDelta_417_; lean_object* v_zetaDeltaSet_418_; lean_object* v_lctx_419_; lean_object* v_localInstances_420_; lean_object* v_defEqCtx_x3f_421_; lean_object* v_synthPendingDepth_422_; lean_object* v_customCanUnfoldPredicate_x3f_423_; uint8_t v_univApprox_424_; uint8_t v_inTypeClassResolution_425_; uint8_t v_cacheInferType_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_keyedConfig_416_ = lean_ctor_get(v_a_340_, 0);
v_trackZetaDelta_417_ = lean_ctor_get_uint8(v_a_340_, sizeof(void*)*7);
v_zetaDeltaSet_418_ = lean_ctor_get(v_a_340_, 1);
v_lctx_419_ = lean_ctor_get(v_a_340_, 2);
v_localInstances_420_ = lean_ctor_get(v_a_340_, 3);
v_defEqCtx_x3f_421_ = lean_ctor_get(v_a_340_, 4);
v_synthPendingDepth_422_ = lean_ctor_get(v_a_340_, 5);
v_customCanUnfoldPredicate_x3f_423_ = lean_ctor_get(v_a_340_, 6);
v_univApprox_424_ = lean_ctor_get_uint8(v_a_340_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_425_ = lean_ctor_get_uint8(v_a_340_, sizeof(void*)*7 + 2);
v_cacheInferType_426_ = lean_ctor_get_uint8(v_a_340_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_416_);
v___x_427_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_414_, v_keyedConfig_416_);
lean_inc(v_customCanUnfoldPredicate_x3f_423_);
lean_inc(v_synthPendingDepth_422_);
lean_inc(v_defEqCtx_x3f_421_);
lean_inc_ref(v_localInstances_420_);
lean_inc_ref(v_lctx_419_);
lean_inc(v_zetaDeltaSet_418_);
v___x_428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_zetaDeltaSet_418_);
lean_ctor_set(v___x_428_, 2, v_lctx_419_);
lean_ctor_set(v___x_428_, 3, v_localInstances_420_);
lean_ctor_set(v___x_428_, 4, v_defEqCtx_x3f_421_);
lean_ctor_set(v___x_428_, 5, v_synthPendingDepth_422_);
lean_ctor_set(v___x_428_, 6, v_customCanUnfoldPredicate_x3f_423_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7, v_trackZetaDelta_417_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7 + 1, v_univApprox_424_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7 + 2, v_inTypeClassResolution_425_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7 + 3, v_cacheInferType_426_);
v___x_429_ = l_Lean_Meta_reduceProj_x3f(v___x_413_, v___x_428_, v_a_341_, v_a_342_, v_a_343_);
lean_dec_ref_known(v___x_428_, 7);
v___y_361_ = v___x_429_;
goto v___jp_360_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_reduceProj_x3f(v___x_413_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
v___y_361_ = v___x_430_;
goto v___jp_360_;
}
v___jp_360_:
{
if (lean_obj_tag(v___y_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_402_; 
v_a_362_ = lean_ctor_get(v___y_361_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___y_361_);
if (v_isSharedCheck_402_ == 0)
{
v___x_364_ = v___y_361_;
v_isShared_365_ = v_isSharedCheck_402_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___y_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_402_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
if (lean_obj_tag(v_a_362_) == 1)
{
lean_object* v_val_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_397_; 
lean_del_object(v___x_364_);
v_val_366_ = lean_ctor_get(v_a_362_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_397_ == 0)
{
v___x_368_ = v_a_362_;
v_isShared_369_ = v_isSharedCheck_397_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_val_366_);
lean_dec(v_a_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_397_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_dummy_370_; lean_object* v_nargs_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_dummy_370_ = lean_obj_once(&l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0, &l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0_once, _init_l_Lean_Meta_Sym_reduceZetaDelta_x3f___closed__0);
v_nargs_371_ = l_Lean_Expr_getAppNumArgs(v_val_359_);
lean_inc(v_nargs_371_);
v___x_372_ = lean_mk_array(v_nargs_371_, v_dummy_370_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_sub(v_nargs_371_, v___x_373_);
lean_dec(v_nargs_371_);
v___x_375_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_359_, v___x_372_, v___x_374_);
v___x_376_ = l_Lean_mkAppN(v_val_366_, v___x_375_);
lean_dec_ref(v___x_375_);
v___x_377_ = l_Lean_Meta_Sym_shareCommon(v___x_376_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_388_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_388_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_388_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_388_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_a_378_);
v___x_383_ = v___x_368_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_385_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_del_object(v___x_368_);
v_a_389_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_377_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_377_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_dec(v_a_362_);
lean_dec(v_val_359_);
v___x_398_ = lean_box(0);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_398_);
v___x_400_ = v___x_364_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_val_359_);
v_a_403_ = lean_ctor_get(v___y_361_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___y_361_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___y_361_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___y_361_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_dec(v_a_355_);
v___x_431_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_431_);
v___x_433_ = v___x_357_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
return v___x_354_;
}
}
else
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec_ref(v_e_337_);
v___x_436_ = lean_box(0);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_436_);
v___x_438_ = v___x_350_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec(v_a_348_);
lean_dec_ref(v_e_337_);
v___x_440_ = lean_box(0);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_440_);
v___x_442_ = v___x_350_;
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
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v___x_345_);
lean_dec_ref(v_e_337_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reduceProjApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_337_ = stack[0].m_obj;
lean_object* v_a_338_ = stack[1].m_obj;
lean_object* v_a_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
lean_object* v_a_341_ = stack[4].m_obj;
lean_object* v_a_342_ = stack[5].m_obj;
lean_object* v_a_343_ = stack[6].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceProjApp_x3f___boxed(lean_object* v_e_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Sym_reduceProjApp_x3f(v_e_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
return v_res_456_;
}
}
lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object* v_e_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_457_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_509_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_509_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_509_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_509_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
if (lean_obj_tag(v_a_466_) == 1)
{
lean_object* v_val_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_468_);
v_val_470_ = lean_ctor_get(v_a_466_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_504_ == 0)
{
v___x_472_ = v_a_466_;
v_isShared_473_ = v_isSharedCheck_504_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_val_470_);
lean_dec(v_a_466_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_504_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_Sym_foldProjs(v_val_470_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = l_Lean_Meta_Sym_shareCommonInc(v_a_475_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v_a_477_);
v___x_482_ = v___x_472_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_486_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_del_object(v___x_472_);
v_a_488_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_476_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_476_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_472_);
v_a_496_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_474_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_474_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec(v_a_466_);
v___x_505_ = lean_box(0);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_505_);
v___x_507_ = v___x_468_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
return v___x_465_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_reduceMatcherApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_457_ = stack[0].m_obj;
lean_object* v_a_458_ = stack[1].m_obj;
lean_object* v_a_459_ = stack[2].m_obj;
lean_object* v_a_460_ = stack[3].m_obj;
lean_object* v_a_461_ = stack[4].m_obj;
lean_object* v_a_462_ = stack[5].m_obj;
lean_object* v_a_463_ = stack[6].m_obj;
lean_object* v_res_510_;
v_res_510_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f___boxed(lean_object* v_e_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec_ref(v_e_511_);
return v_res_519_;
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
