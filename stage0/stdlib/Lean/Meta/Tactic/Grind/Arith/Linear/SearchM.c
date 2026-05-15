// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.SearchM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2);
v___x_9_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
lean_ctor_set(v___x_9_, 3, v___x_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3);
v___x_11_ = lean_box(0);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_14_ = lean_box(0);
v___x_15_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4);
v___x_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(lean_object* v_a_19_, lean_object* v_s_20_){
_start:
{
lean_object* v_structs_21_; lean_object* v_typeIdOf_22_; lean_object* v_exprToStructId_23_; lean_object* v_exprToStructIdEntries_24_; lean_object* v_forbiddenNatModules_25_; lean_object* v_natStructs_26_; lean_object* v_natTypeIdOf_27_; lean_object* v_exprToNatStructId_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v_structs_21_ = lean_ctor_get(v_s_20_, 0);
v_typeIdOf_22_ = lean_ctor_get(v_s_20_, 1);
v_exprToStructId_23_ = lean_ctor_get(v_s_20_, 2);
v_exprToStructIdEntries_24_ = lean_ctor_get(v_s_20_, 3);
v_forbiddenNatModules_25_ = lean_ctor_get(v_s_20_, 4);
v_natStructs_26_ = lean_ctor_get(v_s_20_, 5);
v_natTypeIdOf_27_ = lean_ctor_get(v_s_20_, 6);
v_exprToNatStructId_28_ = lean_ctor_get(v_s_20_, 7);
v___x_29_ = lean_array_get_size(v_structs_21_);
v___x_30_ = lean_nat_dec_lt(v_a_19_, v___x_29_);
if (v___x_30_ == 0)
{
return v_s_20_;
}
else
{
lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_90_; 
lean_inc_ref(v_exprToNatStructId_28_);
lean_inc_ref(v_natTypeIdOf_27_);
lean_inc_ref(v_natStructs_26_);
lean_inc_ref(v_forbiddenNatModules_25_);
lean_inc_ref(v_exprToStructIdEntries_24_);
lean_inc_ref(v_exprToStructId_23_);
lean_inc_ref(v_typeIdOf_22_);
lean_inc_ref(v_structs_21_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_s_20_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; lean_object* v_unused_94_; lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; 
v_unused_91_ = lean_ctor_get(v_s_20_, 7);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_s_20_, 6);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_s_20_, 5);
lean_dec(v_unused_93_);
v_unused_94_ = lean_ctor_get(v_s_20_, 4);
lean_dec(v_unused_94_);
v_unused_95_ = lean_ctor_get(v_s_20_, 3);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_s_20_, 2);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_s_20_, 1);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_s_20_, 0);
lean_dec(v_unused_98_);
v___x_32_ = v_s_20_;
v_isShared_33_ = v_isSharedCheck_90_;
goto v_resetjp_31_;
}
else
{
lean_dec(v_s_20_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_90_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v_v_34_; lean_object* v_id_35_; lean_object* v_ringId_x3f_36_; lean_object* v_type_37_; lean_object* v_u_38_; lean_object* v_intModuleInst_39_; lean_object* v_leInst_x3f_40_; lean_object* v_ltInst_x3f_41_; lean_object* v_lawfulOrderLTInst_x3f_42_; lean_object* v_isPreorderInst_x3f_43_; lean_object* v_orderedAddInst_x3f_44_; lean_object* v_isLinearInst_x3f_45_; lean_object* v_noNatDivInst_x3f_46_; lean_object* v_ringInst_x3f_47_; lean_object* v_commRingInst_x3f_48_; lean_object* v_orderedRingInst_x3f_49_; lean_object* v_fieldInst_x3f_50_; lean_object* v_charInst_x3f_51_; lean_object* v_zero_52_; lean_object* v_ofNatZero_53_; lean_object* v_one_x3f_54_; lean_object* v_leFn_x3f_55_; lean_object* v_ltFn_x3f_56_; lean_object* v_addFn_57_; lean_object* v_zsmulFn_58_; lean_object* v_nsmulFn_59_; lean_object* v_zsmulFn_x3f_60_; lean_object* v_nsmulFn_x3f_61_; lean_object* v_homomulFn_x3f_62_; lean_object* v_subFn_63_; lean_object* v_negFn_64_; lean_object* v_vars_65_; lean_object* v_varMap_66_; lean_object* v_lowers_67_; lean_object* v_uppers_68_; lean_object* v_diseqs_69_; lean_object* v_assignment_70_; lean_object* v_conflict_x3f_71_; lean_object* v_diseqSplits_72_; lean_object* v_elimEqs_73_; lean_object* v_elimStack_74_; lean_object* v_occurs_75_; lean_object* v_ignored_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_89_; 
v_v_34_ = lean_array_fget(v_structs_21_, v_a_19_);
v_id_35_ = lean_ctor_get(v_v_34_, 0);
v_ringId_x3f_36_ = lean_ctor_get(v_v_34_, 1);
v_type_37_ = lean_ctor_get(v_v_34_, 2);
v_u_38_ = lean_ctor_get(v_v_34_, 3);
v_intModuleInst_39_ = lean_ctor_get(v_v_34_, 4);
v_leInst_x3f_40_ = lean_ctor_get(v_v_34_, 5);
v_ltInst_x3f_41_ = lean_ctor_get(v_v_34_, 6);
v_lawfulOrderLTInst_x3f_42_ = lean_ctor_get(v_v_34_, 7);
v_isPreorderInst_x3f_43_ = lean_ctor_get(v_v_34_, 8);
v_orderedAddInst_x3f_44_ = lean_ctor_get(v_v_34_, 9);
v_isLinearInst_x3f_45_ = lean_ctor_get(v_v_34_, 10);
v_noNatDivInst_x3f_46_ = lean_ctor_get(v_v_34_, 11);
v_ringInst_x3f_47_ = lean_ctor_get(v_v_34_, 12);
v_commRingInst_x3f_48_ = lean_ctor_get(v_v_34_, 13);
v_orderedRingInst_x3f_49_ = lean_ctor_get(v_v_34_, 14);
v_fieldInst_x3f_50_ = lean_ctor_get(v_v_34_, 15);
v_charInst_x3f_51_ = lean_ctor_get(v_v_34_, 16);
v_zero_52_ = lean_ctor_get(v_v_34_, 17);
v_ofNatZero_53_ = lean_ctor_get(v_v_34_, 18);
v_one_x3f_54_ = lean_ctor_get(v_v_34_, 19);
v_leFn_x3f_55_ = lean_ctor_get(v_v_34_, 20);
v_ltFn_x3f_56_ = lean_ctor_get(v_v_34_, 21);
v_addFn_57_ = lean_ctor_get(v_v_34_, 22);
v_zsmulFn_58_ = lean_ctor_get(v_v_34_, 23);
v_nsmulFn_59_ = lean_ctor_get(v_v_34_, 24);
v_zsmulFn_x3f_60_ = lean_ctor_get(v_v_34_, 25);
v_nsmulFn_x3f_61_ = lean_ctor_get(v_v_34_, 26);
v_homomulFn_x3f_62_ = lean_ctor_get(v_v_34_, 27);
v_subFn_63_ = lean_ctor_get(v_v_34_, 28);
v_negFn_64_ = lean_ctor_get(v_v_34_, 29);
v_vars_65_ = lean_ctor_get(v_v_34_, 30);
v_varMap_66_ = lean_ctor_get(v_v_34_, 31);
v_lowers_67_ = lean_ctor_get(v_v_34_, 32);
v_uppers_68_ = lean_ctor_get(v_v_34_, 33);
v_diseqs_69_ = lean_ctor_get(v_v_34_, 34);
v_assignment_70_ = lean_ctor_get(v_v_34_, 35);
v_conflict_x3f_71_ = lean_ctor_get(v_v_34_, 36);
v_diseqSplits_72_ = lean_ctor_get(v_v_34_, 37);
v_elimEqs_73_ = lean_ctor_get(v_v_34_, 38);
v_elimStack_74_ = lean_ctor_get(v_v_34_, 39);
v_occurs_75_ = lean_ctor_get(v_v_34_, 40);
v_ignored_76_ = lean_ctor_get(v_v_34_, 41);
v_isSharedCheck_89_ = !lean_is_exclusive(v_v_34_);
if (v_isSharedCheck_89_ == 0)
{
v___x_78_ = v_v_34_;
v_isShared_79_ = v_isSharedCheck_89_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_ignored_76_);
lean_inc(v_occurs_75_);
lean_inc(v_elimStack_74_);
lean_inc(v_elimEqs_73_);
lean_inc(v_diseqSplits_72_);
lean_inc(v_conflict_x3f_71_);
lean_inc(v_assignment_70_);
lean_inc(v_diseqs_69_);
lean_inc(v_uppers_68_);
lean_inc(v_lowers_67_);
lean_inc(v_varMap_66_);
lean_inc(v_vars_65_);
lean_inc(v_negFn_64_);
lean_inc(v_subFn_63_);
lean_inc(v_homomulFn_x3f_62_);
lean_inc(v_nsmulFn_x3f_61_);
lean_inc(v_zsmulFn_x3f_60_);
lean_inc(v_nsmulFn_59_);
lean_inc(v_zsmulFn_58_);
lean_inc(v_addFn_57_);
lean_inc(v_ltFn_x3f_56_);
lean_inc(v_leFn_x3f_55_);
lean_inc(v_one_x3f_54_);
lean_inc(v_ofNatZero_53_);
lean_inc(v_zero_52_);
lean_inc(v_charInst_x3f_51_);
lean_inc(v_fieldInst_x3f_50_);
lean_inc(v_orderedRingInst_x3f_49_);
lean_inc(v_commRingInst_x3f_48_);
lean_inc(v_ringInst_x3f_47_);
lean_inc(v_noNatDivInst_x3f_46_);
lean_inc(v_isLinearInst_x3f_45_);
lean_inc(v_orderedAddInst_x3f_44_);
lean_inc(v_isPreorderInst_x3f_43_);
lean_inc(v_lawfulOrderLTInst_x3f_42_);
lean_inc(v_ltInst_x3f_41_);
lean_inc(v_leInst_x3f_40_);
lean_inc(v_intModuleInst_39_);
lean_inc(v_u_38_);
lean_inc(v_type_37_);
lean_inc(v_ringId_x3f_36_);
lean_inc(v_id_35_);
lean_dec(v_v_34_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_89_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v_xs_x27_81_; lean_object* v___x_83_; 
v___x_80_ = lean_box(0);
v_xs_x27_81_ = lean_array_fset(v_structs_21_, v_a_19_, v___x_80_);
if (v_isShared_79_ == 0)
{
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_id_35_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_ringId_x3f_36_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_type_37_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v_u_38_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v_intModuleInst_39_);
lean_ctor_set(v_reuseFailAlloc_88_, 5, v_leInst_x3f_40_);
lean_ctor_set(v_reuseFailAlloc_88_, 6, v_ltInst_x3f_41_);
lean_ctor_set(v_reuseFailAlloc_88_, 7, v_lawfulOrderLTInst_x3f_42_);
lean_ctor_set(v_reuseFailAlloc_88_, 8, v_isPreorderInst_x3f_43_);
lean_ctor_set(v_reuseFailAlloc_88_, 9, v_orderedAddInst_x3f_44_);
lean_ctor_set(v_reuseFailAlloc_88_, 10, v_isLinearInst_x3f_45_);
lean_ctor_set(v_reuseFailAlloc_88_, 11, v_noNatDivInst_x3f_46_);
lean_ctor_set(v_reuseFailAlloc_88_, 12, v_ringInst_x3f_47_);
lean_ctor_set(v_reuseFailAlloc_88_, 13, v_commRingInst_x3f_48_);
lean_ctor_set(v_reuseFailAlloc_88_, 14, v_orderedRingInst_x3f_49_);
lean_ctor_set(v_reuseFailAlloc_88_, 15, v_fieldInst_x3f_50_);
lean_ctor_set(v_reuseFailAlloc_88_, 16, v_charInst_x3f_51_);
lean_ctor_set(v_reuseFailAlloc_88_, 17, v_zero_52_);
lean_ctor_set(v_reuseFailAlloc_88_, 18, v_ofNatZero_53_);
lean_ctor_set(v_reuseFailAlloc_88_, 19, v_one_x3f_54_);
lean_ctor_set(v_reuseFailAlloc_88_, 20, v_leFn_x3f_55_);
lean_ctor_set(v_reuseFailAlloc_88_, 21, v_ltFn_x3f_56_);
lean_ctor_set(v_reuseFailAlloc_88_, 22, v_addFn_57_);
lean_ctor_set(v_reuseFailAlloc_88_, 23, v_zsmulFn_58_);
lean_ctor_set(v_reuseFailAlloc_88_, 24, v_nsmulFn_59_);
lean_ctor_set(v_reuseFailAlloc_88_, 25, v_zsmulFn_x3f_60_);
lean_ctor_set(v_reuseFailAlloc_88_, 26, v_nsmulFn_x3f_61_);
lean_ctor_set(v_reuseFailAlloc_88_, 27, v_homomulFn_x3f_62_);
lean_ctor_set(v_reuseFailAlloc_88_, 28, v_subFn_63_);
lean_ctor_set(v_reuseFailAlloc_88_, 29, v_negFn_64_);
lean_ctor_set(v_reuseFailAlloc_88_, 30, v_vars_65_);
lean_ctor_set(v_reuseFailAlloc_88_, 31, v_varMap_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 32, v_lowers_67_);
lean_ctor_set(v_reuseFailAlloc_88_, 33, v_uppers_68_);
lean_ctor_set(v_reuseFailAlloc_88_, 34, v_diseqs_69_);
lean_ctor_set(v_reuseFailAlloc_88_, 35, v_assignment_70_);
lean_ctor_set(v_reuseFailAlloc_88_, 36, v_conflict_x3f_71_);
lean_ctor_set(v_reuseFailAlloc_88_, 37, v_diseqSplits_72_);
lean_ctor_set(v_reuseFailAlloc_88_, 38, v_elimEqs_73_);
lean_ctor_set(v_reuseFailAlloc_88_, 39, v_elimStack_74_);
lean_ctor_set(v_reuseFailAlloc_88_, 40, v_occurs_75_);
lean_ctor_set(v_reuseFailAlloc_88_, 41, v_ignored_76_);
v___x_83_ = v_reuseFailAlloc_88_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_86_; 
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*42, v___x_30_);
v___x_84_ = lean_array_fset(v_xs_x27_81_, v_a_19_, v___x_83_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_84_);
v___x_86_ = v___x_32_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_typeIdOf_22_);
lean_ctor_set(v_reuseFailAlloc_87_, 2, v_exprToStructId_23_);
lean_ctor_set(v_reuseFailAlloc_87_, 3, v_exprToStructIdEntries_24_);
lean_ctor_set(v_reuseFailAlloc_87_, 4, v_forbiddenNatModules_25_);
lean_ctor_set(v_reuseFailAlloc_87_, 5, v_natStructs_26_);
lean_ctor_set(v_reuseFailAlloc_87_, 6, v_natTypeIdOf_27_);
lean_ctor_set(v_reuseFailAlloc_87_, 7, v_exprToNatStructId_28_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed(lean_object* v_a_99_, lean_object* v_s_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(v_a_99_, v_s_100_);
lean_dec(v_a_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_ngen_105_; lean_object* v_namePrefix_106_; lean_object* v_idx_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_136_; 
v___x_104_ = lean_st_ref_get(v___y_102_);
v_ngen_105_ = lean_ctor_get(v___x_104_, 2);
lean_inc_ref(v_ngen_105_);
lean_dec(v___x_104_);
v_namePrefix_106_ = lean_ctor_get(v_ngen_105_, 0);
v_idx_107_ = lean_ctor_get(v_ngen_105_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_ngen_105_);
if (v_isSharedCheck_136_ == 0)
{
v___x_109_ = v_ngen_105_;
v_isShared_110_ = v_isSharedCheck_136_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_idx_107_);
lean_inc(v_namePrefix_106_);
lean_dec(v_ngen_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_136_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v_env_112_; lean_object* v_nextMacroScope_113_; lean_object* v_auxDeclNGen_114_; lean_object* v_traceState_115_; lean_object* v_cache_116_; lean_object* v_messages_117_; lean_object* v_infoState_118_; lean_object* v_snapshotTasks_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_134_; 
v___x_111_ = lean_st_ref_take(v___y_102_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
v_nextMacroScope_113_ = lean_ctor_get(v___x_111_, 1);
v_auxDeclNGen_114_ = lean_ctor_get(v___x_111_, 3);
v_traceState_115_ = lean_ctor_get(v___x_111_, 4);
v_cache_116_ = lean_ctor_get(v___x_111_, 5);
v_messages_117_ = lean_ctor_get(v___x_111_, 6);
v_infoState_118_ = lean_ctor_get(v___x_111_, 7);
v_snapshotTasks_119_ = lean_ctor_get(v___x_111_, 8);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v___x_111_, 2);
lean_dec(v_unused_135_);
v___x_121_ = v___x_111_;
v_isShared_122_ = v_isSharedCheck_134_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snapshotTasks_119_);
lean_inc(v_infoState_118_);
lean_inc(v_messages_117_);
lean_inc(v_cache_116_);
lean_inc(v_traceState_115_);
lean_inc(v_auxDeclNGen_114_);
lean_inc(v_nextMacroScope_113_);
lean_inc(v_env_112_);
lean_dec(v___x_111_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_134_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_r_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_idx_107_);
lean_inc(v_namePrefix_106_);
v_r_123_ = l_Lean_Name_num___override(v_namePrefix_106_, v_idx_107_);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_idx_107_, v___x_124_);
lean_dec(v_idx_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_125_);
v___x_127_ = v___x_109_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_namePrefix_106_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_133_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 2, v___x_127_);
v___x_129_ = v___x_121_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_env_112_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_nextMacroScope_113_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_auxDeclNGen_114_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v_traceState_115_);
lean_ctor_set(v_reuseFailAlloc_132_, 5, v_cache_116_);
lean_ctor_set(v_reuseFailAlloc_132_, 6, v_messages_117_);
lean_ctor_set(v_reuseFailAlloc_132_, 7, v_infoState_118_);
lean_ctor_set(v_reuseFailAlloc_132_, 8, v_snapshotTasks_119_);
v___x_129_ = v_reuseFailAlloc_132_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_st_ref_set(v___y_102_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_r_123_);
return v___x_131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg___boxed(lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(v___y_137_);
lean_dec(v___y_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v___x_153_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(v___y_151_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
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
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0___boxed(lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec(v___y_164_);
lean_dec(v___y_163_);
lean_dec(v___y_162_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase(lean_object* v_c_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref(v___x_190_);
v___x_192_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v_cases_195_; lean_object* v_decVars_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_226_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref(v___x_192_);
v___x_194_ = lean_st_ref_take(v_a_177_);
v_cases_195_ = lean_ctor_get(v___x_194_, 0);
v_decVars_196_ = lean_ctor_get(v___x_194_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_226_ == 0)
{
v___x_198_ = v___x_194_;
v_isShared_199_ = v_isSharedCheck_226_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_decVars_196_);
lean_inc(v_cases_195_);
lean_dec(v___x_194_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_226_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc_n(v_a_191_, 2);
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_c_176_);
lean_ctor_set(v___x_200_, 1, v_a_191_);
lean_ctor_set(v___x_200_, 2, v_a_193_);
v___x_201_ = l_Lean_PersistentArray_push___redArg(v_cases_195_, v___x_200_);
v___x_202_ = l_Lean_FVarIdSet_insert(v_decVars_196_, v_a_191_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_202_);
lean_ctor_set(v___x_198_, 0, v___x_201_);
v___x_204_ = v___x_198_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_225_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_205_ = lean_st_ref_set(v_a_177_, v___x_204_);
lean_inc(v_a_178_);
v___f_206_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed), 2, 1);
lean_closure_set(v___f_206_, 0, v_a_178_);
v___x_207_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_208_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_207_, v___f_206_, v_a_179_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v___x_208_, 0);
lean_dec(v_unused_216_);
v___x_210_ = v___x_208_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_dec(v___x_208_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v_a_191_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_191_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_191_);
v_a_217_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_208_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_208_);
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
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_191_);
lean_dec_ref(v_c_176_);
v_a_227_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_192_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_192_);
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
else
{
lean_dec_ref(v_c_176_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkCase___boxed(lean_object* v_c_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Meta_Grind_Arith_Linear_mkCase(v_c_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec(v_a_238_);
lean_dec(v_a_237_);
lean_dec(v_a_236_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(v___y_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___boxed(lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
lean_dec(v___y_265_);
lean_dec(v___y_264_);
return v_res_277_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
}
#ifdef __cplusplus
}
#endif
