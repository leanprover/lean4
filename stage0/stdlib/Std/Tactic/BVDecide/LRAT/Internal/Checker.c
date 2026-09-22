// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Checker
// Imports: import Std.Tactic.BVDecide.LRAT.Internal.Add import Std.Tactic.BVDecide.LRAT.Internal.Delete import Std.Tactic.BVDecide.LRAT.Internal.Rup import Std.Tactic.BVDecide.LRAT.Internal.Empty import Std.Tactic.BVDecide.LRAT.Internal.Rat public import Std.Tactic.BVDecide.LRAT.Actions import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_Clause_ofLiterals___redArg(lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF(lean_object*);
static lean_once_cell_t l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0___closed__0;
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_check___boxed(lean_object*, lean_object*);
static lean_object* _init_l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0(lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
if (lean_obj_tag(v_a_3_) == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_array_to_list(v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_33_; 
v_head_6_ = lean_ctor_get(v_a_3_, 0);
v_tail_7_ = lean_ctor_get(v_a_3_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_33_ == 0)
{
v___x_9_ = v_a_3_;
v_isShared_10_ = v_isSharedCheck_33_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_tail_7_);
lean_inc(v_head_6_);
lean_dec(v_a_3_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_33_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v_val_12_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_obj_once(&l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0___closed__0, &l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0___closed__0_once, _init_l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0___closed__0);
v___x_16_ = lean_int_dec_lt(v___x_15_, v_head_6_);
if (v___x_16_ == 0)
{
uint8_t v___x_17_; 
v___x_17_ = lean_int_dec_lt(v_head_6_, v___x_15_);
if (v___x_17_ == 0)
{
lean_del_object(v___x_9_);
lean_dec(v_head_6_);
v_a_3_ = v_tail_7_;
goto _start;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_19_ = lean_nat_abs(v_head_6_);
lean_dec(v_head_6_);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_nat_sub(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(v___x_16_);
if (v_isShared_10_ == 0)
{
lean_ctor_set_tag(v___x_9_, 0);
lean_ctor_set(v___x_9_, 1, v___x_22_);
lean_ctor_set(v___x_9_, 0, v___x_21_);
v___x_24_ = v___x_9_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
v_val_12_ = v___x_24_;
goto v___jp_11_;
}
}
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_26_ = lean_nat_abs(v_head_6_);
lean_dec(v_head_6_);
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_sub(v___x_26_, v___x_27_);
lean_dec(v___x_26_);
v___x_29_ = lean_box(v___x_16_);
if (v_isShared_10_ == 0)
{
lean_ctor_set_tag(v___x_9_, 0);
lean_ctor_set(v___x_9_, 1, v___x_29_);
lean_ctor_set(v___x_9_, 0, v___x_28_);
v___x_31_ = v___x_9_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
v_val_12_ = v___x_31_;
goto v___jp_11_;
}
}
v___jp_11_:
{
lean_object* v___x_13_; 
v___x_13_ = lean_array_push(v_a_4_, v_val_12_);
v_a_3_ = v_tail_7_;
v_a_4_ = v___x_13_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause(lean_object* v_clause_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = lean_array_to_list(v_clause_36_);
v___x_38_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause___closed__0));
v___x_39_ = l_List_filterMapTR_go___at___00__private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause_spec__0(v___x_37_, v___x_38_);
v___x_40_ = l_Std_Sat_CNF_Clause_ofLiterals___redArg(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go(lean_object* v_state_41_, lean_object* v_proof_42_, lean_object* v_idx_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_array_get_size(v_proof_42_);
v___x_45_ = lean_nat_dec_lt(v_idx_43_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec(v_idx_43_);
lean_dec_ref(v_state_41_);
return v___x_45_;
}
else
{
lean_object* v_step_46_; 
v_step_46_ = lean_array_fget_borrowed(v_proof_42_, v_idx_43_);
switch(lean_obj_tag(v_step_46_))
{
case 0:
{
lean_object* v_rupHints_47_; uint8_t v___x_48_; 
lean_dec(v_idx_43_);
v_rupHints_47_ = lean_ctor_get(v_step_46_, 1);
v___x_48_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty(v_state_41_, v_rupHints_47_);
lean_dec_ref(v_state_41_);
return v___x_48_;
}
case 1:
{
lean_object* v_c_49_; lean_object* v_rupHints_50_; lean_object* v_clause_51_; uint8_t v___x_52_; 
v_c_49_ = lean_ctor_get(v_step_46_, 1);
v_rupHints_50_ = lean_ctor_get(v_step_46_, 2);
lean_inc(v_c_49_);
v_clause_51_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause(v_c_49_);
v___x_52_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_state_41_, v_clause_51_, v_rupHints_50_);
if (v___x_52_ == 0)
{
lean_dec_ref(v_clause_51_);
lean_dec(v_idx_43_);
lean_dec_ref(v_state_41_);
return v___x_52_;
}
else
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_clause_51_);
v___x_54_ = lean_array_push(v_state_41_, v___x_53_);
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_idx_43_, v___x_55_);
lean_dec(v_idx_43_);
v_state_41_ = v___x_54_;
v_idx_43_ = v___x_56_;
goto _start;
}
}
case 2:
{
lean_object* v_pivot_58_; lean_object* v_c_59_; lean_object* v_rupHints_60_; lean_object* v_ratHints_61_; lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_pivot_58_ = lean_ctor_get(v_step_46_, 2);
lean_inc_ref(v_pivot_58_);
v_c_59_ = lean_ctor_get(v_step_46_, 1);
v_rupHints_60_ = lean_ctor_get(v_step_46_, 3);
v_ratHints_61_ = lean_ctor_get(v_step_46_, 4);
v_fst_62_ = lean_ctor_get(v_pivot_58_, 0);
v_snd_63_ = lean_ctor_get(v_pivot_58_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_pivot_58_);
if (v_isSharedCheck_78_ == 0)
{
v___x_65_ = v_pivot_58_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
lean_dec(v_pivot_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_clause_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
lean_inc(v_c_59_);
v_clause_67_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_convertClause(v_c_59_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_sub(v_fst_62_, v___x_68_);
lean_dec(v_fst_62_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_69_);
v___x_71_ = v___x_65_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_snd_63_);
v___x_71_ = v_reuseFailAlloc_77_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
uint8_t v___x_72_; 
lean_inc_ref(v_ratHints_61_);
v___x_72_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRat(v_state_41_, v_clause_67_, v___x_71_, v_rupHints_60_, v_ratHints_61_);
if (v___x_72_ == 0)
{
lean_dec_ref(v_clause_67_);
lean_dec(v_idx_43_);
lean_dec_ref(v_state_41_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_clause_67_);
v___x_74_ = lean_array_push(v_state_41_, v___x_73_);
v___x_75_ = lean_nat_add(v_idx_43_, v___x_68_);
lean_dec(v_idx_43_);
v_state_41_ = v___x_74_;
v_idx_43_ = v___x_75_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_ids_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_ids_79_ = lean_ctor_get(v_step_46_, 0);
v___x_80_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_deleteMany(v_state_41_, v_ids_79_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_idx_43_, v___x_81_);
lean_dec(v_idx_43_);
v_state_41_ = v___x_80_;
v_idx_43_ = v___x_82_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go___boxed(lean_object* v_state_84_, lean_object* v_proof_85_, lean_object* v_idx_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go(v_state_84_, v_proof_85_, v_idx_86_);
lean_dec_ref(v_proof_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go_match__1_splitter___redArg(lean_object* v_step_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_, lean_object* v_h__3_92_, lean_object* v_h__4_93_){
_start:
{
switch(lean_obj_tag(v_step_89_))
{
case 0:
{
lean_object* v_id_94_; lean_object* v_rupHints_95_; lean_object* v___x_96_; 
lean_dec(v_h__4_93_);
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
v_id_94_ = lean_ctor_get(v_step_89_, 0);
lean_inc(v_id_94_);
v_rupHints_95_ = lean_ctor_get(v_step_89_, 1);
lean_inc_ref(v_rupHints_95_);
lean_dec_ref_known(v_step_89_, 2);
v___x_96_ = lean_apply_2(v_h__1_90_, v_id_94_, v_rupHints_95_);
return v___x_96_;
}
case 1:
{
lean_object* v_id_97_; lean_object* v_c_98_; lean_object* v_rupHints_99_; lean_object* v___x_100_; 
lean_dec(v_h__4_93_);
lean_dec(v_h__3_92_);
lean_dec(v_h__1_90_);
v_id_97_ = lean_ctor_get(v_step_89_, 0);
lean_inc(v_id_97_);
v_c_98_ = lean_ctor_get(v_step_89_, 1);
lean_inc(v_c_98_);
v_rupHints_99_ = lean_ctor_get(v_step_89_, 2);
lean_inc_ref(v_rupHints_99_);
lean_dec_ref_known(v_step_89_, 3);
v___x_100_ = lean_apply_3(v_h__2_91_, v_id_97_, v_c_98_, v_rupHints_99_);
return v___x_100_;
}
case 2:
{
lean_object* v_id_101_; lean_object* v_c_102_; lean_object* v_pivot_103_; lean_object* v_rupHints_104_; lean_object* v_ratHints_105_; lean_object* v___x_106_; 
lean_dec(v_h__4_93_);
lean_dec(v_h__2_91_);
lean_dec(v_h__1_90_);
v_id_101_ = lean_ctor_get(v_step_89_, 0);
lean_inc(v_id_101_);
v_c_102_ = lean_ctor_get(v_step_89_, 1);
lean_inc(v_c_102_);
v_pivot_103_ = lean_ctor_get(v_step_89_, 2);
lean_inc_ref(v_pivot_103_);
v_rupHints_104_ = lean_ctor_get(v_step_89_, 3);
lean_inc_ref(v_rupHints_104_);
v_ratHints_105_ = lean_ctor_get(v_step_89_, 4);
lean_inc_ref(v_ratHints_105_);
lean_dec_ref_known(v_step_89_, 5);
v___x_106_ = lean_apply_5(v_h__3_92_, v_id_101_, v_c_102_, v_pivot_103_, v_rupHints_104_, v_ratHints_105_);
return v___x_106_;
}
default: 
{
lean_object* v_ids_107_; lean_object* v___x_108_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
lean_dec(v_h__1_90_);
v_ids_107_ = lean_ctor_get(v_step_89_, 0);
lean_inc_ref(v_ids_107_);
lean_dec_ref_known(v_step_89_, 1);
v___x_108_ = lean_apply_1(v_h__4_93_, v_ids_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go_match__1_splitter(lean_object* v_motive_109_, lean_object* v_step_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_, lean_object* v_h__4_114_){
_start:
{
switch(lean_obj_tag(v_step_110_))
{
case 0:
{
lean_object* v_id_115_; lean_object* v_rupHints_116_; lean_object* v___x_117_; 
lean_dec(v_h__4_114_);
lean_dec(v_h__3_113_);
lean_dec(v_h__2_112_);
v_id_115_ = lean_ctor_get(v_step_110_, 0);
lean_inc(v_id_115_);
v_rupHints_116_ = lean_ctor_get(v_step_110_, 1);
lean_inc_ref(v_rupHints_116_);
lean_dec_ref_known(v_step_110_, 2);
v___x_117_ = lean_apply_2(v_h__1_111_, v_id_115_, v_rupHints_116_);
return v___x_117_;
}
case 1:
{
lean_object* v_id_118_; lean_object* v_c_119_; lean_object* v_rupHints_120_; lean_object* v___x_121_; 
lean_dec(v_h__4_114_);
lean_dec(v_h__3_113_);
lean_dec(v_h__1_111_);
v_id_118_ = lean_ctor_get(v_step_110_, 0);
lean_inc(v_id_118_);
v_c_119_ = lean_ctor_get(v_step_110_, 1);
lean_inc(v_c_119_);
v_rupHints_120_ = lean_ctor_get(v_step_110_, 2);
lean_inc_ref(v_rupHints_120_);
lean_dec_ref_known(v_step_110_, 3);
v___x_121_ = lean_apply_3(v_h__2_112_, v_id_118_, v_c_119_, v_rupHints_120_);
return v___x_121_;
}
case 2:
{
lean_object* v_id_122_; lean_object* v_c_123_; lean_object* v_pivot_124_; lean_object* v_rupHints_125_; lean_object* v_ratHints_126_; lean_object* v___x_127_; 
lean_dec(v_h__4_114_);
lean_dec(v_h__2_112_);
lean_dec(v_h__1_111_);
v_id_122_ = lean_ctor_get(v_step_110_, 0);
lean_inc(v_id_122_);
v_c_123_ = lean_ctor_get(v_step_110_, 1);
lean_inc(v_c_123_);
v_pivot_124_ = lean_ctor_get(v_step_110_, 2);
lean_inc_ref(v_pivot_124_);
v_rupHints_125_ = lean_ctor_get(v_step_110_, 3);
lean_inc_ref(v_rupHints_125_);
v_ratHints_126_ = lean_ctor_get(v_step_110_, 4);
lean_inc_ref(v_ratHints_126_);
lean_dec_ref_known(v_step_110_, 5);
v___x_127_ = lean_apply_5(v_h__3_113_, v_id_122_, v_c_123_, v_pivot_124_, v_rupHints_125_, v_ratHints_126_);
return v___x_127_;
}
default: 
{
lean_object* v_ids_128_; lean_object* v___x_129_; 
lean_dec(v_h__3_113_);
lean_dec(v_h__2_112_);
lean_dec(v_h__1_111_);
v_ids_128_ = lean_ctor_get(v_step_110_, 0);
lean_inc_ref(v_ids_128_);
lean_dec_ref_known(v_step_110_, 1);
v___x_129_ = lean_apply_1(v_h__4_114_, v_ids_128_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_check(lean_object* v_proof_130_, lean_object* v_formula_131_){
_start:
{
lean_object* v_state_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_state_132_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF(v_formula_131_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Checker_0__Std_Tactic_BVDecide_LRAT_Internal_check_go(v_state_132_, v_proof_130_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_check___boxed(lean_object* v_proof_135_, lean_object* v_formula_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Std_Tactic_BVDecide_LRAT_Internal_check(v_proof_135_, v_formula_136_);
lean_dec_ref(v_proof_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Delete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Checker(builtin);
}
#ifdef __cplusplus
}
#endif
