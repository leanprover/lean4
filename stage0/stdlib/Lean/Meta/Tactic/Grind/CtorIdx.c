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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_14_; lean_object* v___x_63935__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
v___x_63935__overap_15_ = lean_panic_fn(v___x_14_, v_msg_2_);
v___x_16_ = lean_apply_11(v___x_63935__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* v_msg_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v_msg_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_355_; 
v_val_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_355_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_355_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_355_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; 
v___x_67_ = l_isCtorIdx_x3f___redArg(v_val_63_, v___y_54_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_346_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_346_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_346_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_346_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
if (lean_obj_tag(v_a_68_) == 1)
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_341_; 
v_val_72_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_341_ == 0)
{
v___x_74_ = v_a_68_;
v_isShared_75_ = v_isSharedCheck_341_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_a_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_341_;
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
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
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
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_332_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_332_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_332_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_332_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_self_96_; uint8_t v_ctor_97_; uint8_t v_heqProofs_98_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; 
v_self_96_ = lean_ctor_get(v_a_92_, 0);
lean_inc_ref(v_self_96_);
v_ctor_97_ = lean_ctor_get_uint8(v_a_92_, sizeof(void*)*11 + 2);
v_heqProofs_98_ = lean_ctor_get_uint8(v_a_92_, sizeof(void*)*11 + 4);
lean_dec(v_a_92_);
if (v_ctor_97_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_e_41_);
v___x_155_ = lean_box(0);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_155_);
v___x_157_ = v___x_94_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
lean_object* v___x_159_; 
lean_del_object(v___x_94_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc_ref(v_self_96_);
v___x_159_ = l_Lean_Meta_isConstructorApp_x3f(v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_323_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_323_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_323_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_323_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
if (lean_obj_tag(v_a_160_) == 1)
{
lean_object* v_val_164_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; 
lean_del_object(v___x_162_);
v_val_164_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_val_164_);
lean_dec_ref(v_a_160_);
if (v_heqProofs_98_ == 0)
{
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v___y_166_ = v___y_45_;
v___y_167_ = v___y_46_;
v___y_168_ = v___y_47_;
v___y_169_ = v___y_48_;
v___y_170_ = v___y_49_;
v___y_171_ = v___y_50_;
v___y_172_ = v___y_51_;
v___y_173_ = v___y_52_;
v___y_174_ = v___y_53_;
v___y_175_ = v___y_54_;
goto v___jp_165_;
}
else
{
lean_object* v___x_225_; 
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc_ref(v_self_96_);
lean_inc(v___x_90_);
v___x_225_ = l_Lean_Meta_Grind_hasSameType(v___x_90_, v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; uint8_t v___x_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_225_);
v___x_227_ = lean_unbox(v_a_226_);
lean_dec(v_a_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v_val_164_);
lean_dec_ref(v_e_41_);
v___x_228_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_90_, v___y_45_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_228_);
v___x_230_ = l_Lean_Meta_Grind_getGeneration___redArg(v_self_96_, v___y_45_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___y_233_; uint8_t v___x_294_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v___x_294_ = lean_nat_dec_le(v_a_229_, v_a_231_);
if (v___x_294_ == 0)
{
lean_dec(v_a_231_);
v___y_233_ = v_a_229_;
goto v___jp_232_;
}
else
{
lean_dec(v_a_229_);
v___y_233_ = v_a_231_;
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_234_; 
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc(v___x_90_);
v___x_234_ = lean_infer_type(v___x_90_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_234_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___x_236_ = l_Lean_Meta_whnfD(v_a_235_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
lean_inc_ref(v_self_96_);
v___x_238_ = lean_infer_type(v_self_96_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref(v___x_238_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___y_52_);
lean_inc_ref(v___y_51_);
v___x_240_ = l_Lean_Meta_whnfD(v_a_239_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_261_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_261_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_261_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_261_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_name_245_; uint8_t v___x_246_; 
v_name_245_ = lean_ctor_get(v_toConstantVal_76_, 0);
lean_inc(v_name_245_);
lean_dec_ref(v_toConstantVal_76_);
lean_inc(v___x_80_);
v___x_246_ = l_Lean_Expr_isAppOfArity(v_a_237_, v_name_245_, v___x_80_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_name_245_);
lean_del_object(v___x_243_);
lean_dec(v_a_241_);
lean_dec(v_a_237_);
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v___x_247_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
v___x_248_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v___x_247_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Expr_isAppOfArity(v_a_241_, v_name_245_, v___x_80_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec(v_name_245_);
lean_dec(v_a_241_);
lean_dec(v_a_237_);
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v___x_250_ = lean_box(0);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_250_);
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_object* v___x_254_; lean_object* v_env_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
lean_del_object(v___x_243_);
v___x_254_ = lean_st_ref_get(v___y_54_);
v_env_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v_env_255_);
lean_dec(v___x_254_);
v___x_256_ = l_Lean_Expr_getAppFn(v_a_237_);
v___x_257_ = l_Lean_Expr_constLevels_x21(v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(v_name_245_);
v___x_259_ = l_Lean_Environment_containsOnBranch(v_env_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
lean_inc(v___x_258_);
v___x_260_ = l_Lean_executeReservedNameAction(v___x_258_, v___y_53_, v___y_54_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_dec_ref(v___x_260_);
v___y_100_ = v_a_237_;
v___y_101_ = v___x_257_;
v___y_102_ = v___y_233_;
v___y_103_ = v_a_241_;
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
lean_dec(v___x_258_);
lean_dec(v___x_257_);
lean_dec(v_a_241_);
lean_dec(v_a_237_);
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
return v___x_260_;
}
}
else
{
v___y_100_ = v_a_237_;
v___y_101_ = v___x_257_;
v___y_102_ = v___y_233_;
v___y_103_ = v_a_241_;
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
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_a_237_);
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v_a_262_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_240_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_240_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_237_);
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v_a_270_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_238_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_238_);
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
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v_a_278_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_236_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_236_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec(v___y_233_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v_a_286_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_234_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_234_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_a_229_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v_a_295_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_230_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_230_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
v_a_303_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_228_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_228_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
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
v___y_166_ = v___y_45_;
v___y_167_ = v___y_46_;
v___y_168_ = v___y_47_;
v___y_169_ = v___y_48_;
v___y_170_ = v___y_49_;
v___y_171_ = v___y_50_;
v___y_172_ = v___y_51_;
v___y_173_ = v___y_52_;
v___y_174_ = v___y_53_;
v___y_175_ = v___y_54_;
goto v___jp_165_;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_val_164_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_e_41_);
v_a_311_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_225_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_225_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
v___jp_165_:
{
lean_object* v_cidx_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_cidx_176_ = lean_ctor_get(v_val_164_, 2);
lean_inc(v_cidx_176_);
lean_dec(v_val_164_);
v___x_177_ = l_Lean_mkNatLit(v_cidx_176_);
v___x_178_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_177_, v___y_171_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref(v___x_178_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_box(0);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v___y_167_);
lean_inc(v___y_166_);
lean_inc(v_a_179_);
v___x_182_ = lean_grind_internalize(v_a_179_, v___x_180_, v___x_181_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; 
lean_dec_ref(v___x_182_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc_ref(v___y_168_);
lean_inc(v___y_166_);
v___x_183_ = lean_grind_mk_eq_proof(v___x_90_, v_self_96_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = l_Lean_Expr_appFn_x21(v_e_41_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
v___x_186_ = l_Lean_Meta_mkCongrArg(v___x_185_, v_a_184_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref(v___x_186_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v_a_179_);
lean_inc_ref(v_e_41_);
v___x_188_ = l_Lean_Meta_mkEq(v_e_41_, v_a_179_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v___x_188_);
v___x_190_ = l_Lean_Meta_mkExpectedPropHint(v_a_187_, v_a_189_);
v___x_191_ = 0;
v___x_192_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_41_, v_a_179_, v___x_190_, v___x_191_, v___y_166_, v___y_168_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_166_);
return v___x_192_;
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_a_187_);
lean_dec(v_a_179_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_166_);
lean_dec_ref(v_e_41_);
v_a_193_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_188_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_179_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_166_);
lean_dec_ref(v_e_41_);
v_a_201_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_186_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_186_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec(v_a_179_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_166_);
lean_dec_ref(v_e_41_);
v_a_209_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_183_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_183_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_dec(v_a_179_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec_ref(v_e_41_);
return v___x_182_;
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec_ref(v_e_41_);
v_a_217_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_178_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_178_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
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
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v_a_160_);
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_e_41_);
v___x_319_ = lean_box(0);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_319_);
v___x_321_ = v___x_162_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_self_96_);
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_e_41_);
v_a_324_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_159_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_159_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v___jp_99_:
{
lean_object* v___x_115_; lean_object* v_dummy_116_; lean_object* v_nargs_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_nargs_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc(v___y_104_);
v___x_115_ = l_Lean_mkConst(v___y_104_, v___y_101_);
v_dummy_116_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_117_ = l_Lean_Expr_getAppNumArgs(v___y_100_);
lean_inc(v_nargs_117_);
v___x_118_ = lean_mk_array(v_nargs_117_, v_dummy_116_);
v___x_119_ = lean_nat_sub(v_nargs_117_, v___x_81_);
lean_dec(v_nargs_117_);
v___x_120_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_100_, v___x_118_, v___x_119_);
v___x_121_ = l_Lean_mkAppN(v___x_115_, v___x_120_);
lean_dec_ref(v___x_120_);
v___x_122_ = l_Lean_Expr_app___override(v___x_121_, v___x_90_);
v_nargs_123_ = l_Lean_Expr_getAppNumArgs(v___y_103_);
lean_inc(v_nargs_123_);
v___x_124_ = lean_mk_array(v_nargs_123_, v_dummy_116_);
v___x_125_ = lean_nat_sub(v_nargs_123_, v___x_81_);
lean_dec(v_nargs_123_);
v___x_126_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_103_, v___x_124_, v___x_125_);
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
lean_ctor_set(v___x_74_, 0, v___y_104_);
v___x_132_ = v___x_74_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___y_104_);
v___x_132_ = v_reuseFailAlloc_146_;
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
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_145_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_addNewRawFact(v___x_128_, v_a_130_, v___y_102_, v___x_134_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_143_; 
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_144_);
v___x_137_ = v___x_135_;
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
else
{
lean_dec(v___x_135_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v___x_128_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
lean_dec(v___y_104_);
lean_dec(v___y_102_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
v_a_147_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_129_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_129_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v___x_90_);
lean_dec(v___x_80_);
lean_dec_ref(v_toConstantVal_76_);
lean_del_object(v___x_74_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_e_41_);
v_a_333_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_91_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_91_);
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
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_342_ = lean_box(0);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_342_);
v___x_344_ = v___x_70_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_del_object(v___x_65_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v_a_347_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_67_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_67_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v___x_62_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v_x_43_);
lean_dec_ref(v_e_41_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* v_e_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_358_, v_x_359_, v_x_360_, v_x_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* v_e_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_dummy_386_; lean_object* v_nargs_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_dummy_386_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_387_ = l_Lean_Expr_getAppNumArgs(v_e_374_);
lean_inc(v_nargs_387_);
v___x_388_ = lean_mk_array(v_nargs_387_, v_dummy_386_);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_sub(v_nargs_387_, v___x_389_);
lean_dec(v_nargs_387_);
lean_inc_ref(v_e_374_);
v___x_391_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_374_, v_e_374_, v___x_388_, v___x_390_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Grind_propagateCtorIdxUp(v_e_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
return v_res_404_;
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
