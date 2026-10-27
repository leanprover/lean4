// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CtorIdx
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Constructions.CtorIdx import Lean.Meta.CtorIdxHInj
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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Tactic.Grind.CtorIdx"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Grind.propagateCtorIdxUp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = "assertion violation: aType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices)\n      -- both types should be headed by the same type former\n      "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_50046__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
v___x_50046__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
v___x_16_ = lean_apply_11(v___x_50046__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec(v___y_18_);
return v_res_29_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0(void){
_start:
{
lean_object* v___x_30_; lean_object* v_dummy_31_; 
v___x_30_ = lean_box(0);
v_dummy_31_ = l_Lean_Expr_sort___override(v___x_30_);
return v_dummy_31_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3));
v___x_36_ = lean_unsigned_to_nat(6u);
v___x_37_ = lean_unsigned_to_nat(37u);
v___x_38_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2));
v___x_39_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1));
v___x_40_ = l_mkPanicMessageWithDecl(v___x_39_, v___x_38_, v___x_37_, v___x_36_, v___x_35_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* v_e_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
if (lean_obj_tag(v_x_42_) == 5)
{
lean_object* v_fn_56_; lean_object* v_arg_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_fn_56_ = lean_ctor_get(v_x_42_, 0);
lean_inc_ref(v_fn_56_);
v_arg_57_ = lean_ctor_get(v_x_42_, 1);
lean_inc_ref(v_arg_57_);
lean_dec_ref_known(v_x_42_, 2);
v___x_58_ = lean_array_set(v_x_43_, v_x_44_, v_arg_57_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_sub(v_x_44_, v___x_59_);
lean_dec(v_x_44_);
v_x_42_ = v_fn_56_;
v_x_43_ = v___x_58_;
v_x_44_ = v___x_60_;
goto _start;
}
else
{
lean_object* v___x_62_; 
lean_dec(v_x_44_);
v___x_62_ = l_Lean_Expr_constName_x3f(v_x_42_);
lean_dec_ref(v_x_42_);
if (lean_obj_tag(v___x_62_) == 1)
{
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_352_; 
v_val_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_352_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_352_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_352_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = l_Lean_instInhabitedExpr;
v___x_68_ = l_Lean_isCtorIdx_x3f___redArg(v_val_63_, v___y_54_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_343_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_343_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_343_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_343_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
if (lean_obj_tag(v_a_69_) == 1)
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_338_; 
v_val_73_ = lean_ctor_get(v_a_69_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_69_);
if (v_isSharedCheck_338_ == 0)
{
v___x_75_ = v_a_69_;
v_isShared_76_ = v_isSharedCheck_338_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v_a_69_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_338_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v_toConstantVal_77_; lean_object* v_numParams_78_; lean_object* v_numIndices_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_toConstantVal_77_ = lean_ctor_get(v_val_73_, 0);
lean_inc_ref(v_toConstantVal_77_);
v_numParams_78_ = lean_ctor_get(v_val_73_, 1);
lean_inc(v_numParams_78_);
v_numIndices_79_ = lean_ctor_get(v_val_73_, 2);
lean_inc(v_numIndices_79_);
lean_dec(v_val_73_);
v___x_80_ = lean_array_get_size(v_x_43_);
v___x_81_ = lean_nat_add(v_numParams_78_, v_numIndices_79_);
lean_dec(v_numIndices_79_);
lean_dec(v_numParams_78_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v___x_81_, v___x_82_);
v___x_84_ = lean_nat_dec_eq(v___x_80_, v___x_83_);
lean_dec(v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_87_; 
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_85_ = lean_box(0);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_85_);
v___x_87_ = v___x_71_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_del_object(v___x_71_);
v___x_89_ = lean_nat_sub(v___x_80_, v___x_82_);
v___x_90_ = lean_array_get(v___x_67_, v_x_43_, v___x_89_);
lean_dec(v___x_89_);
lean_dec_ref(v_x_43_);
lean_inc(v___x_90_);
v___x_91_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_90_, v___y_45_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_329_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_329_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_329_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_329_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_self_96_; uint8_t v_ctor_97_; uint8_t v_heqProofs_98_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; 
v_self_96_ = lean_ctor_get(v_a_92_, 0);
lean_inc_ref(v_self_96_);
v_ctor_97_ = lean_ctor_get_uint8(v_a_92_, sizeof(void*)*12 + 2);
v_heqProofs_98_ = lean_ctor_get_uint8(v_a_92_, sizeof(void*)*12 + 4);
lean_dec(v_a_92_);
if (v_ctor_97_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_154_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v___x_152_ = lean_box(0);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_152_);
v___x_154_ = v___x_94_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_156_; 
lean_del_object(v___x_94_);
lean_inc_ref(v_self_96_);
v___x_156_ = l_Lean_Meta_isConstructorApp_x3f(v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_320_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_320_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_320_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_320_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
if (lean_obj_tag(v_a_157_) == 1)
{
lean_object* v_val_161_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; 
lean_del_object(v___x_159_);
v_val_161_ = lean_ctor_get(v_a_157_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v_a_157_, 1);
if (v_heqProofs_98_ == 0)
{
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v___y_163_ = v___y_45_;
v___y_164_ = v___y_46_;
v___y_165_ = v___y_47_;
v___y_166_ = v___y_48_;
v___y_167_ = v___y_49_;
v___y_168_ = v___y_50_;
v___y_169_ = v___y_51_;
v___y_170_ = v___y_52_;
v___y_171_ = v___y_53_;
v___y_172_ = v___y_54_;
goto v___jp_162_;
}
else
{
lean_object* v___x_222_; 
lean_inc_ref(v_self_96_);
lean_inc(v___x_90_);
v___x_222_ = l_Lean_Meta_Grind_hasSameType(v___x_90_, v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; uint8_t v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = lean_unbox(v_a_223_);
lean_dec(v_a_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec(v_val_161_);
lean_dec_ref(v_e_41_);
v___x_225_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_90_, v___y_45_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = l_Lean_Meta_Grind_getGeneration___redArg(v_self_96_, v___y_45_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___y_230_; uint8_t v___x_291_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_291_ = lean_nat_dec_le(v_a_226_, v_a_228_);
if (v___x_291_ == 0)
{
lean_dec(v_a_228_);
v___y_230_ = v_a_226_;
goto v___jp_229_;
}
else
{
lean_dec(v_a_226_);
v___y_230_ = v_a_228_;
goto v___jp_229_;
}
v___jp_229_:
{
lean_object* v___x_231_; 
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___x_90_);
v___x_231_ = lean_infer_type(v___x_90_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = l_Lean_Meta_whnfD(v_a_232_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc_ref(v_self_96_);
v___x_235_ = lean_infer_type(v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = l_Lean_Meta_whnfD(v_a_236_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_258_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_258_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_258_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_258_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_name_242_; uint8_t v___x_243_; 
v_name_242_ = lean_ctor_get(v_toConstantVal_77_, 0);
lean_inc(v_name_242_);
lean_dec_ref(v_toConstantVal_77_);
lean_inc(v___x_81_);
v___x_243_ = l_Lean_Expr_isAppOfArity(v_a_234_, v_name_242_, v___x_81_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_name_242_);
lean_del_object(v___x_240_);
lean_dec(v_a_238_);
lean_dec(v_a_234_);
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v___x_244_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
v___x_245_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v___x_244_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v___x_245_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = l_Lean_Expr_isAppOfArity(v_a_238_, v_name_242_, v___x_81_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_name_242_);
lean_dec(v_a_238_);
lean_dec(v_a_234_);
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v___x_247_ = lean_box(0);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_247_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_env_255_; uint8_t v___x_256_; 
lean_del_object(v___x_240_);
v___x_251_ = l_Lean_Expr_getAppFn(v_a_234_);
v___x_252_ = l_Lean_Expr_constLevels_x21(v___x_251_);
lean_dec_ref(v___x_251_);
v___x_253_ = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(v_name_242_);
v___x_254_ = lean_st_ref_get(v___y_54_);
v_env_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v_env_255_);
lean_dec(v___x_254_);
v___x_256_ = l_Lean_Environment_containsOnBranch(v_env_255_, v___x_253_);
lean_dec_ref(v_env_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_inc(v___x_253_);
v___x_257_ = l_Lean_executeReservedNameAction(v___x_253_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_dec_ref_known(v___x_257_, 1);
v___y_100_ = v_a_234_;
v___y_101_ = v___y_230_;
v___y_102_ = v_a_238_;
v___y_103_ = v___x_252_;
v___y_104_ = v___x_253_;
v___y_105_ = v___y_45_;
v___y_106_ = v___y_47_;
v___y_107_ = v___y_51_;
v___y_108_ = v___y_52_;
v___y_109_ = v___y_53_;
v___y_110_ = v___y_54_;
goto v___jp_99_;
}
else
{
lean_dec(v___x_253_);
lean_dec(v___x_252_);
lean_dec(v_a_238_);
lean_dec(v_a_234_);
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
return v___x_257_;
}
}
else
{
v___y_100_ = v_a_234_;
v___y_101_ = v___y_230_;
v___y_102_ = v_a_238_;
v___y_103_ = v___x_252_;
v___y_104_ = v___x_253_;
v___y_105_ = v___y_45_;
v___y_106_ = v___y_47_;
v___y_107_ = v___y_51_;
v___y_108_ = v___y_52_;
v___y_109_ = v___y_53_;
v___y_110_ = v___y_54_;
goto v___jp_99_;
}
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_a_234_);
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_259_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_237_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_237_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_a_234_);
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_267_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_235_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_235_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_275_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_233_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_233_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v___y_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_283_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_231_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_231_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_a_226_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_292_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_227_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_227_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_300_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_225_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_225_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v___y_163_ = v___y_45_;
v___y_164_ = v___y_46_;
v___y_165_ = v___y_47_;
v___y_166_ = v___y_48_;
v___y_167_ = v___y_49_;
v___y_168_ = v___y_50_;
v___y_169_ = v___y_51_;
v___y_170_ = v___y_52_;
v___y_171_ = v___y_53_;
v___y_172_ = v___y_54_;
goto v___jp_162_;
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_val_161_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v_a_308_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_222_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_222_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
v___jp_162_:
{
lean_object* v_cidx_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_cidx_173_ = lean_ctor_get(v_val_161_, 2);
lean_inc(v_cidx_173_);
lean_dec(v_val_161_);
v___x_174_ = l_Lean_mkNatLit(v_cidx_173_);
v___x_175_ = l_Lean_Meta_Sym_shareCommon(v___x_174_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc_n(v_a_176_, 2);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_box(0);
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
lean_inc(v___y_164_);
lean_inc(v___y_163_);
v___x_179_ = lean_grind_internalize(v_a_176_, v___x_177_, v___x_178_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v___x_180_; 
lean_dec_ref_known(v___x_179_, 1);
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
lean_inc(v___y_164_);
lean_inc(v___y_163_);
v___x_180_ = lean_grind_mk_eq_proof(v___x_90_, v_self_96_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = l_Lean_Expr_appFn_x21(v_e_41_);
v___x_183_ = l_Lean_Meta_mkCongrArg(v___x_182_, v_a_181_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
lean_inc(v_a_176_);
lean_inc_ref(v_e_41_);
v___x_185_ = l_Lean_Meta_mkEq(v_e_41_, v_a_176_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = l_Lean_Meta_mkExpectedPropHint(v_a_184_, v_a_186_);
v___x_188_ = 0;
v___x_189_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_41_, v_a_176_, v___x_187_, v___x_188_, v___y_163_, v___y_165_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v___x_189_;
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_a_184_);
lean_dec(v_a_176_);
lean_dec_ref(v_e_41_);
v_a_190_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_185_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_185_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
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
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_176_);
lean_dec_ref(v_e_41_);
v_a_198_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_183_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_183_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_176_);
lean_dec_ref(v_e_41_);
v_a_206_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_180_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_180_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_dec(v_a_176_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec_ref(v_e_41_);
return v___x_179_;
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec_ref(v_e_41_);
v_a_214_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_175_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_175_);
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
else
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_a_157_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v___x_316_ = lean_box(0);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_316_);
v___x_318_ = v___x_159_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v_a_321_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_156_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_156_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
v___jp_99_:
{
lean_object* v___x_111_; lean_object* v_dummy_112_; lean_object* v_nargs_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_nargs_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
lean_inc(v___y_104_);
v___x_111_ = l_Lean_mkConst(v___y_104_, v___y_103_);
v_dummy_112_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_113_ = l_Lean_Expr_getAppNumArgs(v___y_100_);
lean_inc(v_nargs_113_);
v___x_114_ = lean_mk_array(v_nargs_113_, v_dummy_112_);
v___x_115_ = lean_nat_sub(v_nargs_113_, v___x_82_);
lean_dec(v_nargs_113_);
v___x_116_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_100_, v___x_114_, v___x_115_);
v___x_117_ = l_Lean_mkAppN(v___x_111_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = l_Lean_Expr_app___override(v___x_117_, v___x_90_);
v_nargs_119_ = l_Lean_Expr_getAppNumArgs(v___y_102_);
lean_inc(v_nargs_119_);
v___x_120_ = lean_mk_array(v_nargs_119_, v_dummy_112_);
v___x_121_ = lean_nat_sub(v_nargs_119_, v___x_82_);
lean_dec(v_nargs_119_);
v___x_122_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_102_, v___x_120_, v___x_121_);
v___x_123_ = l_Lean_mkAppN(v___x_118_, v___x_122_);
lean_dec_ref(v___x_122_);
v___x_124_ = l_Lean_Expr_app___override(v___x_123_, v_self_96_);
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
lean_inc_ref(v___x_124_);
v___x_125_ = lean_infer_type(v___x_124_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v___x_125_, 1);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 0);
lean_ctor_set(v___x_75_, 0, v___y_104_);
v___x_128_ = v___x_75_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___y_104_);
v___x_128_ = v_reuseFailAlloc_143_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 0, v___x_128_);
v___x_130_ = v___x_65_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_142_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(1);
v___x_132_ = l_Lean_Meta_Grind_addNewRawFact___redArg(v___x_124_, v_a_126_, v___y_101_, v___x_130_, v___x_131_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_132_, 0);
lean_dec(v_unused_141_);
v___x_134_ = v___x_132_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_dec(v___x_132_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
return v___x_132_;
}
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec_ref(v___x_124_);
lean_dec(v___y_104_);
lean_dec(v___y_101_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
v_a_144_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_125_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_125_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v___x_90_);
lean_dec(v___x_81_);
lean_dec_ref(v_toConstantVal_77_);
lean_del_object(v___x_75_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v_a_330_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_91_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_91_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_a_69_);
lean_del_object(v___x_65_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_339_ = lean_box(0);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_339_);
v___x_341_ = v___x_71_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_del_object(v___x_65_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v_a_344_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_68_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_68_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v___x_62_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* v_e_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_355_, v_x_356_, v_x_357_, v_x_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_359_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* v_e_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_dummy_383_; lean_object* v_nargs_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_dummy_383_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_384_ = l_Lean_Expr_getAppNumArgs(v_e_371_);
lean_inc(v_nargs_384_);
v___x_385_ = lean_mk_array(v_nargs_384_, v_dummy_383_);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_sub(v_nargs_384_, v___x_386_);
lean_dec(v_nargs_384_);
lean_inc_ref(v_e_371_);
v___x_388_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_371_, v_e_371_, v___x_385_, v___x_387_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* v_e_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_Grind_propagateCtorIdxUp(v_e_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec(v_a_390_);
return v_res_401_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorIdxHInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
