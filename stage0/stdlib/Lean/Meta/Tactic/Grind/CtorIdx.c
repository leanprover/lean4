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
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_50040__overap_15_; lean_object* v___x_16_; 
v___x_14_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
v___x_50040__overap_15_ = lean_panic_fn_borrowed(v___x_14_, v_msg_2_);
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
v___x_16_ = lean_apply_11(v___x_50040__overap_15_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v___y_7_ = stack[5].m_obj;
lean_object* v___y_8_ = stack[6].m_obj;
lean_object* v___y_9_ = stack[7].m_obj;
lean_object* v___y_10_ = stack[8].m_obj;
lean_object* v___y_11_ = stack[9].m_obj;
lean_object* v___y_12_ = stack[10].m_obj;
lean_object* v_res_17_;
v_res_17_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* v_msg_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v_msg_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec(v___y_19_);
return v_res_30_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v_dummy_32_; 
v___x_31_ = lean_box(0);
v_dummy_32_ = l_Lean_Expr_sort___override(v___x_31_);
return v_dummy_32_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_36_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3));
v___x_37_ = lean_unsigned_to_nat(6u);
v___x_38_ = lean_unsigned_to_nat(37u);
v___x_39_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2));
v___x_40_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1));
v___x_41_ = l_mkPanicMessageWithDecl(v___x_40_, v___x_39_, v___x_38_, v___x_37_, v___x_36_);
return v___x_41_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* v_e_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
if (lean_obj_tag(v_x_43_) == 5)
{
lean_object* v_fn_57_; lean_object* v_arg_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_fn_57_ = lean_ctor_get(v_x_43_, 0);
lean_inc_ref(v_fn_57_);
v_arg_58_ = lean_ctor_get(v_x_43_, 1);
lean_inc_ref(v_arg_58_);
lean_dec_ref_known(v_x_43_, 2);
v___x_59_ = lean_array_set(v_x_44_, v_x_45_, v_arg_58_);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_sub(v_x_45_, v___x_60_);
lean_dec(v_x_45_);
v_x_43_ = v_fn_57_;
v_x_44_ = v___x_59_;
v_x_45_ = v___x_61_;
goto _start;
}
else
{
lean_object* v___x_63_; 
lean_dec(v_x_45_);
v___x_63_ = l_Lean_Expr_constName_x3f(v_x_43_);
lean_dec_ref(v_x_43_);
if (lean_obj_tag(v___x_63_) == 1)
{
lean_object* v_val_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_357_; 
v_val_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_357_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_357_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_val_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_357_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = l_Lean_instInhabitedExpr;
v___x_69_ = l_Lean_isCtorIdx_x3f___redArg(v_val_64_, v___y_55_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_348_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_348_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_348_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_348_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
if (lean_obj_tag(v_a_70_) == 1)
{
lean_object* v_val_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_343_; 
v_val_74_ = lean_ctor_get(v_a_70_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_70_);
if (v_isSharedCheck_343_ == 0)
{
v___x_76_ = v_a_70_;
v_isShared_77_ = v_isSharedCheck_343_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_val_74_);
lean_dec(v_a_70_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_343_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v_toConstantVal_78_; lean_object* v_numParams_79_; lean_object* v_numIndices_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_toConstantVal_78_ = lean_ctor_get(v_val_74_, 0);
lean_inc_ref(v_toConstantVal_78_);
v_numParams_79_ = lean_ctor_get(v_val_74_, 1);
lean_inc(v_numParams_79_);
v_numIndices_80_ = lean_ctor_get(v_val_74_, 2);
lean_inc(v_numIndices_80_);
lean_dec(v_val_74_);
v___x_81_ = lean_array_get_size(v_x_44_);
v___x_82_ = lean_nat_add(v_numParams_79_, v_numIndices_80_);
lean_dec(v_numIndices_80_);
lean_dec(v_numParams_79_);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_add(v___x_82_, v___x_83_);
v___x_85_ = lean_nat_dec_eq(v___x_81_, v___x_84_);
lean_dec(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_88_; 
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
lean_dec_ref(v_x_44_);
lean_dec_ref(v_e_42_);
v___x_86_ = lean_box(0);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_86_);
v___x_88_ = v___x_72_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_del_object(v___x_72_);
v___x_90_ = lean_nat_sub(v___x_81_, v___x_83_);
v___x_91_ = lean_array_get(v___x_68_, v_x_44_, v___x_90_);
lean_dec(v___x_90_);
lean_dec_ref(v_x_44_);
lean_inc(v___x_91_);
v___x_92_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_91_, v___y_46_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_334_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_334_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_334_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_334_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_self_97_; uint8_t v_ctor_98_; uint8_t v_heqProofs_99_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; lean_object* v___y_115_; 
v_self_97_ = lean_ctor_get(v_a_93_, 0);
lean_inc_ref(v_self_97_);
v_ctor_98_ = lean_ctor_get_uint8(v_a_93_, sizeof(void*)*12 + 2);
v_heqProofs_99_ = lean_ctor_get_uint8(v_a_93_, sizeof(void*)*12 + 4);
lean_dec(v_a_93_);
if (v_ctor_98_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
lean_dec_ref(v_e_42_);
v___x_157_ = lean_box(0);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_157_);
v___x_159_ = v___x_95_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v___x_161_; 
lean_del_object(v___x_95_);
lean_inc_ref(v_self_97_);
v___x_161_ = l_Lean_Meta_isConstructorApp_x3f(v_self_97_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_325_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_325_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_325_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_325_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
if (lean_obj_tag(v_a_162_) == 1)
{
lean_object* v_val_166_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; 
lean_del_object(v___x_164_);
v_val_166_ = lean_ctor_get(v_a_162_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v_a_162_, 1);
if (v_heqProofs_99_ == 0)
{
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v___y_168_ = v___y_46_;
v___y_169_ = v___y_47_;
v___y_170_ = v___y_48_;
v___y_171_ = v___y_49_;
v___y_172_ = v___y_50_;
v___y_173_ = v___y_51_;
v___y_174_ = v___y_52_;
v___y_175_ = v___y_53_;
v___y_176_ = v___y_54_;
v___y_177_ = v___y_55_;
goto v___jp_167_;
}
else
{
lean_object* v___x_227_; 
lean_inc_ref(v_self_97_);
lean_inc(v___x_91_);
v___x_227_ = l_Lean_Meta_Grind_hasSameType(v___x_91_, v_self_97_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; uint8_t v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = lean_unbox(v_a_228_);
lean_dec(v_a_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_dec(v_val_166_);
lean_dec_ref(v_e_42_);
v___x_230_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_91_, v___y_46_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_Lean_Meta_Grind_getGeneration___redArg(v_self_97_, v___y_46_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___y_235_; uint8_t v___x_296_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_296_ = lean_nat_dec_le(v_a_231_, v_a_233_);
if (v___x_296_ == 0)
{
lean_dec(v_a_233_);
v___y_235_ = v_a_231_;
goto v___jp_234_;
}
else
{
lean_dec(v_a_231_);
v___y_235_ = v_a_233_;
goto v___jp_234_;
}
v___jp_234_:
{
lean_object* v___x_236_; 
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc(v___x_91_);
v___x_236_ = lean_infer_type(v___x_91_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = l_Lean_Meta_whnfD(v_a_237_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc_ref(v_self_97_);
v___x_240_ = lean_infer_type(v_self_97_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_Meta_whnfD(v_a_241_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_263_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_263_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_name_247_; uint8_t v___x_248_; 
v_name_247_ = lean_ctor_get(v_toConstantVal_78_, 0);
lean_inc(v_name_247_);
lean_dec_ref(v_toConstantVal_78_);
lean_inc(v___x_82_);
v___x_248_ = l_Lean_Expr_isAppOfArity(v_a_239_, v_name_247_, v___x_82_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_name_247_);
lean_del_object(v___x_245_);
lean_dec(v_a_243_);
lean_dec(v_a_239_);
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v___x_249_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
v___x_250_ = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(v___x_249_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
return v___x_250_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_Expr_isAppOfArity(v_a_243_, v_name_247_, v___x_82_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec(v_name_247_);
lean_dec(v_a_243_);
lean_dec(v_a_239_);
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v___x_252_ = lean_box(0);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_252_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_env_260_; uint8_t v___x_261_; 
lean_del_object(v___x_245_);
v___x_256_ = l_Lean_Expr_getAppFn(v_a_239_);
v___x_257_ = l_Lean_Expr_constLevels_x21(v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(v_name_247_);
v___x_259_ = lean_st_ref_get(v___y_55_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v___x_261_ = l_Lean_Environment_containsOnBranch(v_env_260_, v___x_258_);
lean_dec_ref(v_env_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_inc(v___x_258_);
v___x_262_ = l_Lean_executeReservedNameAction(v___x_258_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_dec_ref_known(v___x_262_, 1);
v___y_101_ = v___x_257_;
v___y_102_ = v___x_258_;
v___y_103_ = v___y_235_;
v___y_104_ = v_a_239_;
v___y_105_ = v_a_243_;
v___y_106_ = v___y_46_;
v___y_107_ = v___y_47_;
v___y_108_ = v___y_48_;
v___y_109_ = v___y_49_;
v___y_110_ = v___y_50_;
v___y_111_ = v___y_51_;
v___y_112_ = v___y_52_;
v___y_113_ = v___y_53_;
v___y_114_ = v___y_54_;
v___y_115_ = v___y_55_;
goto v___jp_100_;
}
else
{
lean_dec(v___x_258_);
lean_dec(v___x_257_);
lean_dec(v_a_243_);
lean_dec(v_a_239_);
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
return v___x_262_;
}
}
else
{
v___y_101_ = v___x_257_;
v___y_102_ = v___x_258_;
v___y_103_ = v___y_235_;
v___y_104_ = v_a_239_;
v___y_105_ = v_a_243_;
v___y_106_ = v___y_46_;
v___y_107_ = v___y_47_;
v___y_108_ = v___y_48_;
v___y_109_ = v___y_49_;
v___y_110_ = v___y_50_;
v___y_111_ = v___y_51_;
v___y_112_ = v___y_52_;
v___y_113_ = v___y_53_;
v___y_114_ = v___y_54_;
v___y_115_ = v___y_55_;
goto v___jp_100_;
}
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_239_);
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_264_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_242_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_242_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec(v_a_239_);
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_272_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_240_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_240_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_280_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_238_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_238_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v___y_235_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_288_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_236_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_236_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_a_231_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_297_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_232_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_232_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
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
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_305_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_230_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_230_);
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
else
{
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v___y_168_ = v___y_46_;
v___y_169_ = v___y_47_;
v___y_170_ = v___y_48_;
v___y_171_ = v___y_49_;
v___y_172_ = v___y_50_;
v___y_173_ = v___y_51_;
v___y_174_ = v___y_52_;
v___y_175_ = v___y_53_;
v___y_176_ = v___y_54_;
v___y_177_ = v___y_55_;
goto v___jp_167_;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_val_166_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
lean_dec_ref(v_e_42_);
v_a_313_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_227_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_227_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
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
v___jp_167_:
{
lean_object* v_cidx_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_cidx_178_ = lean_ctor_get(v_val_166_, 2);
lean_inc(v_cidx_178_);
lean_dec(v_val_166_);
v___x_179_ = l_Lean_mkNatLit(v_cidx_178_);
v___x_180_ = l_Lean_Meta_Sym_shareCommon(v___x_179_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc_n(v_a_181_, 2);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_box(0);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc(v___y_168_);
v___x_184_ = lean_grind_internalize(v_a_181_, v___x_182_, v___x_183_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v___x_185_; 
lean_dec_ref_known(v___x_184_, 1);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
lean_inc(v___y_169_);
lean_inc(v___y_168_);
v___x_185_ = lean_grind_mk_eq_proof(v___x_91_, v_self_97_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = l_Lean_Expr_appFn_x21(v_e_42_);
v___x_188_ = l_Lean_Meta_mkCongrArg(v___x_187_, v_a_186_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
lean_inc(v_a_181_);
lean_inc_ref(v_e_42_);
v___x_190_ = l_Lean_Meta_mkEq(v_e_42_, v_a_181_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = l_Lean_Meta_mkExpectedPropHint(v_a_189_, v_a_191_);
v___x_193_ = 0;
v___x_194_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_42_, v_a_181_, v___x_192_, v___x_193_, v___y_168_, v___y_170_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
return v___x_194_;
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v_a_189_);
lean_dec(v_a_181_);
lean_dec_ref(v_e_42_);
v_a_195_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_190_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_190_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec(v_a_181_);
lean_dec_ref(v_e_42_);
v_a_203_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_188_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_188_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_a_181_);
lean_dec_ref(v_e_42_);
v_a_211_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_185_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_185_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_dec(v_a_181_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec_ref(v_e_42_);
return v___x_184_;
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec_ref(v_e_42_);
v_a_219_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_180_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_180_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
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
}
else
{
lean_object* v___x_321_; lean_object* v___x_323_; 
lean_dec(v_a_162_);
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
lean_dec_ref(v_e_42_);
v___x_321_ = lean_box(0);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_321_);
v___x_323_ = v___x_164_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_self_97_);
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
lean_dec_ref(v_e_42_);
v_a_326_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_161_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_161_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
v___jp_100_:
{
lean_object* v___x_116_; lean_object* v_dummy_117_; lean_object* v_nargs_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_nargs_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_inc(v___y_102_);
v___x_116_ = l_Lean_mkConst(v___y_102_, v___y_101_);
v_dummy_117_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_118_ = l_Lean_Expr_getAppNumArgs(v___y_104_);
lean_inc(v_nargs_118_);
v___x_119_ = lean_mk_array(v_nargs_118_, v_dummy_117_);
v___x_120_ = lean_nat_sub(v_nargs_118_, v___x_83_);
lean_dec(v_nargs_118_);
v___x_121_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_104_, v___x_119_, v___x_120_);
v___x_122_ = l_Lean_mkAppN(v___x_116_, v___x_121_);
lean_dec_ref(v___x_121_);
v___x_123_ = l_Lean_Expr_app___override(v___x_122_, v___x_91_);
v_nargs_124_ = l_Lean_Expr_getAppNumArgs(v___y_105_);
lean_inc(v_nargs_124_);
v___x_125_ = lean_mk_array(v_nargs_124_, v_dummy_117_);
v___x_126_ = lean_nat_sub(v_nargs_124_, v___x_83_);
lean_dec(v_nargs_124_);
v___x_127_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_105_, v___x_125_, v___x_126_);
v___x_128_ = l_Lean_mkAppN(v___x_123_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = l_Lean_Expr_app___override(v___x_128_, v_self_97_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_113_);
lean_inc_ref(v___y_112_);
lean_inc_ref(v___x_129_);
v___x_130_ = lean_infer_type(v___x_129_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 0);
lean_ctor_set(v___x_76_, 0, v___y_102_);
v___x_133_ = v___x_76_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___y_102_);
v___x_133_ = v_reuseFailAlloc_148_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 7);
lean_ctor_set(v___x_66_, 0, v___x_133_);
v___x_135_ = v___x_66_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_147_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(1);
v___x_137_ = l_Lean_Meta_Grind_addNewRawFact(v___x_129_, v_a_131_, v___y_103_, v___x_135_, v___x_136_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_137_, 0);
lean_dec(v_unused_146_);
v___x_139_ = v___x_137_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_dec(v___x_137_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v___x_129_);
lean_dec(v___y_103_);
lean_dec(v___y_102_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
v_a_149_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_130_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_130_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v___x_91_);
lean_dec(v___x_82_);
lean_dec_ref(v_toConstantVal_78_);
lean_del_object(v___x_76_);
lean_del_object(v___x_66_);
lean_dec_ref(v_e_42_);
v_a_335_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_92_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_92_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_346_; 
lean_dec(v_a_70_);
lean_del_object(v___x_66_);
lean_dec_ref(v_x_44_);
lean_dec_ref(v_e_42_);
v___x_344_ = lean_box(0);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_344_);
v___x_346_ = v___x_72_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_del_object(v___x_66_);
lean_dec_ref(v_x_44_);
lean_dec_ref(v_e_42_);
v_a_349_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_69_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_69_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v___x_63_);
lean_dec_ref(v_x_44_);
lean_dec_ref(v_e_42_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_42_ = stack[0].m_obj;
lean_object* v_x_43_ = stack[1].m_obj;
lean_object* v_x_44_ = stack[2].m_obj;
lean_object* v_x_45_ = stack[3].m_obj;
lean_object* v___y_46_ = stack[4].m_obj;
lean_object* v___y_47_ = stack[5].m_obj;
lean_object* v___y_48_ = stack[6].m_obj;
lean_object* v___y_49_ = stack[7].m_obj;
lean_object* v___y_50_ = stack[8].m_obj;
lean_object* v___y_51_ = stack[9].m_obj;
lean_object* v___y_52_ = stack[10].m_obj;
lean_object* v___y_53_ = stack[11].m_obj;
lean_object* v___y_54_ = stack[12].m_obj;
lean_object* v___y_55_ = stack[13].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_42_, v_x_43_, v_x_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* v_e_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_361_, v_x_362_, v_x_363_, v_x_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec(v___y_365_);
return v_res_376_;
}
}
lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* v_e_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_dummy_389_; lean_object* v_nargs_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_dummy_389_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
v_nargs_390_ = l_Lean_Expr_getAppNumArgs(v_e_377_);
lean_inc(v_nargs_390_);
v___x_391_ = lean_mk_array(v_nargs_390_, v_dummy_389_);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_sub(v_nargs_390_, v___x_392_);
lean_dec(v_nargs_390_);
lean_inc_ref(v_e_377_);
v___x_394_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(v_e_377_, v_e_377_, v___x_391_, v___x_393_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
return v___x_394_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateCtorIdxUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_377_ = stack[0].m_obj;
lean_object* v_a_378_ = stack[1].m_obj;
lean_object* v_a_379_ = stack[2].m_obj;
lean_object* v_a_380_ = stack[3].m_obj;
lean_object* v_a_381_ = stack[4].m_obj;
lean_object* v_a_382_ = stack[5].m_obj;
lean_object* v_a_383_ = stack[6].m_obj;
lean_object* v_a_384_ = stack[7].m_obj;
lean_object* v_a_385_ = stack[8].m_obj;
lean_object* v_a_386_ = stack[9].m_obj;
lean_object* v_a_387_ = stack[10].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Lean_Meta_Grind_propagateCtorIdxUp(v_e_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Grind_propagateCtorIdxUp(v_e_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec(v_a_397_);
return v_res_408_;
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
