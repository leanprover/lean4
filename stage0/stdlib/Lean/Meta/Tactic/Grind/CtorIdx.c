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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
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
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_63942__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
v___x_63942__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_63942__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
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
lean_dec_ref(v_x_42_);
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
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_356_; 
v_val_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_356_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_356_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_356_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; 
v___x_67_ = l_isCtorIdx_x3f___redArg(v_val_63_, v___y_54_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_347_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_347_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_347_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_347_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
if (lean_obj_tag(v_a_68_) == 1)
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_342_; 
v_val_72_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_342_ == 0)
{
v___x_74_ = v_a_68_;
v_isShared_75_ = v_isSharedCheck_342_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_a_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_342_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v_toConstantVal_76_; lean_object* v_numParams_77_; lean_object* v_numIndices_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_toConstantVal_76_ = lean_ctor_get(v_val_72_, 0);
lean_inc_ref(v_toConstantVal_76_);
v_numParams_77_ = lean_ctor_get(v_val_72_, 1);
lean_inc(v_numParams_77_);
v_numIndices_78_ = lean_ctor_get(v_val_72_, 2);
lean_inc(v_numIndices_78_);
lean_dec(v_val_72_);
v___x_79_ = lean_array_get_size(v_x_43_);
v___x_80_ = lean_nat_add(v_numParams_77_, v_numIndices_78_);
lean_dec(v_numIndices_78_);
lean_dec(v_numParams_77_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v___x_80_, v___x_81_);
v___x_83_ = lean_nat_dec_eq(v___x_79_, v___x_82_);
lean_dec(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_86_; 
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_84_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_84_);
v___x_86_ = v___x_70_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_del_object(v___x_70_);
v___x_88_ = l_Lean_instInhabitedExpr;
v___x_89_ = lean_nat_sub(v___x_79_, v___x_81_);
v___x_90_ = lean_array_get(v___x_88_, v_x_43_, v___x_89_);
lean_dec(v___x_89_);
lean_dec_ref(v_x_43_);
lean_inc(v___x_90_);
v___x_91_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_90_, v___y_45_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_333_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_333_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_333_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_333_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_self_96_; uint8_t v_ctor_97_; uint8_t v_heqProofs_98_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; 
v_self_96_ = lean_ctor_get(v_a_92_, 0);
lean_inc_ref(v_self_96_);
v_ctor_97_ = lean_ctor_get_uint8(v_a_92_, sizeof(void*)*12 + 2);
v_heqProofs_98_ = lean_ctor_get_uint8(v_a_92_, sizeof(void*)*12 + 4);
lean_dec(v_a_92_);
if (v_ctor_97_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_158_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v___x_156_ = lean_box(0);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_156_);
v___x_158_ = v___x_94_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
else
{
lean_object* v___x_160_; 
lean_del_object(v___x_94_);
lean_inc_ref(v_self_96_);
v___x_160_ = l_Lean_Meta_isConstructorApp_x3f(v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_324_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_324_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_324_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_324_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
if (lean_obj_tag(v_a_161_) == 1)
{
lean_object* v_val_165_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; 
lean_del_object(v___x_163_);
v_val_165_ = lean_ctor_get(v_a_161_, 0);
lean_inc(v_val_165_);
lean_dec_ref(v_a_161_);
if (v_heqProofs_98_ == 0)
{
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v___y_167_ = v___y_45_;
v___y_168_ = v___y_46_;
v___y_169_ = v___y_47_;
v___y_170_ = v___y_48_;
v___y_171_ = v___y_49_;
v___y_172_ = v___y_50_;
v___y_173_ = v___y_51_;
v___y_174_ = v___y_52_;
v___y_175_ = v___y_53_;
v___y_176_ = v___y_54_;
goto v___jp_166_;
}
else
{
lean_object* v___x_226_; 
lean_inc_ref(v_self_96_);
lean_inc(v___x_90_);
v___x_226_ = l_Lean_Meta_Grind_hasSameType(v___x_90_, v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; uint8_t v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = lean_unbox(v_a_227_);
lean_dec(v_a_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_dec(v_val_165_);
lean_dec_ref(v_e_41_);
v___x_229_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_90_, v___y_45_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref(v___x_229_);
v___x_231_ = l_Lean_Meta_Grind_getGeneration___redArg(v_self_96_, v___y_45_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___y_234_; uint8_t v___x_295_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
v___x_295_ = lean_nat_dec_le(v_a_230_, v_a_232_);
if (v___x_295_ == 0)
{
lean_dec(v_a_232_);
v___y_234_ = v_a_230_;
goto v___jp_233_;
}
else
{
lean_dec(v_a_230_);
v___y_234_ = v_a_232_;
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_235_; 
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___x_90_);
v___x_235_ = lean_infer_type(v___x_90_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref(v___x_235_);
v___x_237_ = l_Lean_Meta_whnfD(v_a_236_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref(v___x_237_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc_ref(v_self_96_);
v___x_239_ = lean_infer_type(v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref(v___x_239_);
v___x_241_ = l_Lean_Meta_whnfD(v_a_240_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_262_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_262_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_262_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_262_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_name_246_; uint8_t v___x_247_; 
v_name_246_ = lean_ctor_get(v_toConstantVal_76_, 0);
lean_inc(v_name_246_);
lean_dec_ref(v_toConstantVal_76_);
lean_inc(v___x_80_);
v___x_247_ = l_Lean_Expr_isAppOfArity(v_a_238_, v_name_246_, v___x_80_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_name_246_);
lean_del_object(v___x_244_);
lean_dec(v_a_242_);
lean_dec(v_a_238_);
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v___x_248_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
v___x_249_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v___x_248_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v___x_249_;
}
else
{
uint8_t v___x_250_; 
v___x_250_ = l_Lean_Expr_isAppOfArity(v_a_242_, v_name_246_, v___x_80_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v_name_246_);
lean_dec(v_a_242_);
lean_dec(v_a_238_);
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v___x_251_ = lean_box(0);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_251_);
v___x_253_ = v___x_244_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
else
{
lean_object* v___x_255_; lean_object* v_env_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
lean_del_object(v___x_244_);
v___x_255_ = lean_st_ref_get(v___y_54_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_env_256_);
lean_dec(v___x_255_);
v___x_257_ = l_Lean_Expr_getAppFn(v_a_238_);
v___x_258_ = l_Lean_Expr_constLevels_x21(v___x_257_);
lean_dec_ref(v___x_257_);
v___x_259_ = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(v_name_246_);
v___x_260_ = l_Lean_Environment_containsOnBranch(v_env_256_, v___x_259_);
lean_dec_ref(v_env_256_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_inc(v___x_259_);
v___x_261_ = l_Lean_executeReservedNameAction(v___x_259_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_dec_ref(v___x_261_);
v___y_100_ = v___y_234_;
v___y_101_ = v___x_259_;
v___y_102_ = v_a_242_;
v___y_103_ = v_a_238_;
v___y_104_ = v___x_258_;
v___y_105_ = v___y_45_;
v___y_106_ = v___y_46_;
v___y_107_ = v___y_47_;
v___y_108_ = v___y_48_;
v___y_109_ = v___y_49_;
v___y_110_ = v___y_50_;
v___y_111_ = v___y_51_;
v___y_112_ = v___y_52_;
v___y_113_ = v___y_53_;
v___y_114_ = v___y_54_;
goto v___jp_99_;
}
else
{
lean_dec(v___x_259_);
lean_dec(v___x_258_);
lean_dec(v_a_242_);
lean_dec(v_a_238_);
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
return v___x_261_;
}
}
else
{
v___y_100_ = v___y_234_;
v___y_101_ = v___x_259_;
v___y_102_ = v_a_242_;
v___y_103_ = v_a_238_;
v___y_104_ = v___x_258_;
v___y_105_ = v___y_45_;
v___y_106_ = v___y_46_;
v___y_107_ = v___y_47_;
v___y_108_ = v___y_48_;
v___y_109_ = v___y_49_;
v___y_110_ = v___y_50_;
v___y_111_ = v___y_51_;
v___y_112_ = v___y_52_;
v___y_113_ = v___y_53_;
v___y_114_ = v___y_54_;
goto v___jp_99_;
}
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_a_238_);
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_263_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_241_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_241_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec(v_a_238_);
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_271_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_239_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_239_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_279_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_237_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_237_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec(v___y_234_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_287_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_235_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_235_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_a_230_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_296_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_231_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_231_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_304_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_229_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_229_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v___y_167_ = v___y_45_;
v___y_168_ = v___y_46_;
v___y_169_ = v___y_47_;
v___y_170_ = v___y_48_;
v___y_171_ = v___y_49_;
v___y_172_ = v___y_50_;
v___y_173_ = v___y_51_;
v___y_174_ = v___y_52_;
v___y_175_ = v___y_53_;
v___y_176_ = v___y_54_;
goto v___jp_166_;
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_val_165_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v_a_312_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_226_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_226_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
v___jp_166_:
{
lean_object* v_cidx_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_cidx_177_ = lean_ctor_get(v_val_165_, 2);
lean_inc(v_cidx_177_);
lean_dec(v_val_165_);
v___x_178_ = l_Lean_mkNatLit(v_cidx_177_);
v___x_179_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_178_, v___y_172_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_n(v_a_180_, 2);
lean_dec_ref(v___x_179_);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_box(0);
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
lean_inc(v___y_174_);
lean_inc_ref(v___y_173_);
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc(v___y_167_);
v___x_183_ = lean_grind_internalize(v_a_180_, v___x_181_, v___x_182_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v___x_183_);
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
lean_inc(v___y_174_);
lean_inc_ref(v___y_173_);
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc(v___y_167_);
v___x_184_ = lean_grind_mk_eq_proof(v___x_90_, v_self_96_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref(v___x_184_);
v___x_186_ = l_Lean_Expr_appFn_x21(v_e_41_);
v___x_187_ = l_Lean_Meta_mkCongrArg(v___x_186_, v_a_185_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref(v___x_187_);
lean_inc(v_a_180_);
lean_inc_ref(v_e_41_);
v___x_189_ = l_Lean_Meta_mkEq(v_e_41_, v_a_180_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref(v___x_189_);
v___x_191_ = l_Lean_Meta_mkExpectedPropHint(v_a_188_, v_a_190_);
v___x_192_ = 0;
v___x_193_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_41_, v_a_180_, v___x_191_, v___x_192_, v___y_167_, v___y_169_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
return v___x_193_;
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_a_188_);
lean_dec(v_a_180_);
lean_dec_ref(v_e_41_);
v_a_194_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_189_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_180_);
lean_dec_ref(v_e_41_);
v_a_202_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_187_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_187_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_180_);
lean_dec_ref(v_e_41_);
v_a_210_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_184_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_184_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_dec(v_a_180_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec_ref(v_e_41_);
return v___x_183_;
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec_ref(v_e_41_);
v_a_218_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_179_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_179_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec(v_a_161_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v___x_320_ = lean_box(0);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_320_);
v___x_322_ = v___x_163_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v_a_325_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_160_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_160_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
v___jp_99_:
{
lean_object* v___x_115_; lean_object* v_dummy_116_; lean_object* v_nargs_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_nargs_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc(v___y_101_);
v___x_115_ = l_Lean_mkConst(v___y_101_, v___y_104_);
v_dummy_116_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_117_ = l_Lean_Expr_getAppNumArgs(v___y_103_);
lean_inc(v_nargs_117_);
v___x_118_ = lean_mk_array(v_nargs_117_, v_dummy_116_);
v___x_119_ = lean_nat_sub(v_nargs_117_, v___x_81_);
lean_dec(v_nargs_117_);
v___x_120_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_103_, v___x_118_, v___x_119_);
v___x_121_ = l_Lean_mkAppN(v___x_115_, v___x_120_);
lean_dec_ref(v___x_120_);
v___x_122_ = l_Lean_Expr_app___override(v___x_121_, v___x_90_);
v_nargs_123_ = l_Lean_Expr_getAppNumArgs(v___y_102_);
lean_inc(v_nargs_123_);
v___x_124_ = lean_mk_array(v_nargs_123_, v_dummy_116_);
v___x_125_ = lean_nat_sub(v_nargs_123_, v___x_81_);
lean_dec(v_nargs_123_);
v___x_126_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_102_, v___x_124_, v___x_125_);
v___x_127_ = l_Lean_mkAppN(v___x_122_, v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = l_Lean_Expr_app___override(v___x_127_, v_self_96_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc_ref(v___x_128_);
v___x_129_ = lean_infer_type(v___x_128_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
lean_dec_ref(v___x_129_);
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 0);
lean_ctor_set(v___x_74_, 0, v___y_101_);
v___x_132_ = v___x_74_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___y_101_);
v___x_132_ = v_reuseFailAlloc_147_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 0, v___x_132_);
v___x_134_ = v___x_65_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_146_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(1);
v___x_136_ = l_Lean_Meta_Grind_addNewRawFact(v___x_128_, v_a_130_, v___y_100_, v___x_134_, v___x_135_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_144_; 
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_136_, 0);
lean_dec(v_unused_145_);
v___x_138_ = v___x_136_;
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
else
{
lean_dec(v___x_136_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_144_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_140_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec_ref(v___x_128_);
lean_dec(v___y_101_);
lean_dec(v___y_100_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_148_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_129_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_129_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec_ref(v_e_41_);
v_a_334_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_91_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_91_);
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
}
else
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_343_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_343_);
v___x_345_ = v___x_70_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_del_object(v___x_65_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v_a_348_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_67_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_67_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_62_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* v_e_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_359_, v_x_360_, v_x_361_, v_x_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec(v___y_363_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_dummy_387_; lean_object* v_nargs_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_dummy_387_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_388_ = l_Lean_Expr_getAppNumArgs(v_e_375_);
lean_inc(v_nargs_388_);
v___x_389_ = lean_mk_array(v_nargs_388_, v_dummy_387_);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_sub(v_nargs_388_, v___x_390_);
lean_dec(v_nargs_388_);
lean_inc_ref(v_e_375_);
v___x_392_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_375_, v_e_375_, v___x_389_, v___x_391_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Grind_propagateCtorIdxUp(v_e_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec(v_a_394_);
return v_res_405_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
