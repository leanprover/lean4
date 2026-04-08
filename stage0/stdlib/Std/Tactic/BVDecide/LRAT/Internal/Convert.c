// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Convert
// Imports: public import Std.Sat.CNF.RelabelFin public import Std.Tactic.BVDecide.LRAT.Internal.Formula import Init.Data.Array.Bootstrap
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0(lean_object* v_lit_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_add(v_lit_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0___boxed(lean_object* v_lit_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lam__0(v_lit_4_);
lean_dec(v_lit_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(lean_object* v_cnf_7_){
_start:
{
lean_object* v___f_8_; lean_object* v_cnf_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__0));
v_cnf_9_ = l_Std_Sat_CNF_relabelFin(v_cnf_7_);
v___x_10_ = l_Std_Sat_CNF_relabel___redArg(v___f_8_, v_cnf_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(lean_object* v_n_11_, lean_object* v_clause_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_array_mk(v_clause_12_);
v___x_14_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(v_n_11_, v___x_13_);
lean_dec_ref(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27___boxed(lean_object* v_n_15_, lean_object* v_clause_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(v_n_15_, v_clause_16_);
lean_dec(v_n_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(lean_object* v_n_18_, lean_object* v_as_19_, size_t v_i_20_, size_t v_stop_21_, lean_object* v_b_22_){
_start:
{
lean_object* v___y_24_; uint8_t v___x_28_; 
v___x_28_ = lean_usize_dec_eq(v_i_20_, v_stop_21_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_array_uget_borrowed(v_as_19_, v_i_20_);
lean_inc(v___x_29_);
v___x_30_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(v_n_18_, v___x_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
v___y_24_ = v_b_22_;
goto v___jp_23_;
}
else
{
lean_object* v___x_31_; 
v___x_31_ = lean_array_push(v_b_22_, v___x_30_);
v___y_24_ = v___x_31_;
goto v___jp_23_;
}
}
else
{
return v_b_22_;
}
v___jp_23_:
{
size_t v___x_25_; size_t v___x_26_; 
v___x_25_ = ((size_t)1ULL);
v___x_26_ = lean_usize_add(v_i_20_, v___x_25_);
v_i_20_ = v___x_26_;
v_b_22_ = v___y_24_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0___boxed(lean_object* v_n_32_, lean_object* v_as_33_, lean_object* v_i_34_, lean_object* v_stop_35_, lean_object* v_b_36_){
_start:
{
size_t v_i_boxed_37_; size_t v_stop_boxed_38_; lean_object* v_res_39_; 
v_i_boxed_37_ = lean_unbox_usize(v_i_34_);
lean_dec(v_i_34_);
v_stop_boxed_38_ = lean_unbox_usize(v_stop_35_);
lean_dec(v_stop_35_);
v_res_39_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(v_n_32_, v_as_33_, v_i_boxed_37_, v_stop_boxed_38_, v_b_36_);
lean_dec_ref(v_as_33_);
lean_dec(v_n_32_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(lean_object* v_n_42_, lean_object* v_as_43_, lean_object* v_start_44_, lean_object* v_stop_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___closed__0));
v___x_47_ = lean_nat_dec_lt(v_start_44_, v_stop_45_);
if (v___x_47_ == 0)
{
return v___x_46_;
}
else
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_array_get_size(v_as_43_);
v___x_49_ = lean_nat_dec_le(v_stop_45_, v___x_48_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_nat_dec_lt(v_start_44_, v___x_48_);
if (v___x_50_ == 0)
{
return v___x_46_;
}
else
{
size_t v___x_51_; size_t v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_usize_of_nat(v_start_44_);
v___x_52_ = lean_usize_of_nat(v___x_48_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(v_n_42_, v_as_43_, v___x_51_, v___x_52_, v___x_46_);
return v___x_53_;
}
}
else
{
size_t v___x_54_; size_t v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_usize_of_nat(v_start_44_);
v___x_55_ = lean_usize_of_nat(v_stop_45_);
v___x_56_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0_spec__0(v_n_42_, v_as_43_, v___x_54_, v___x_55_, v___x_46_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0___boxed(lean_object* v_n_57_, lean_object* v_as_58_, lean_object* v_start_59_, lean_object* v_stop_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(v_n_57_, v_as_58_, v_start_59_, v_stop_60_);
lean_dec(v_stop_60_);
lean_dec(v_start_59_);
lean_dec_ref(v_as_58_);
lean_dec(v_n_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(lean_object* v_n_62_, lean_object* v_clauses_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_array_get_size(v_clauses_63_);
v___x_66_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_spec__0(v_n_62_, v_clauses_63_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___boxed(lean_object* v_n_67_, lean_object* v_clauses_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(v_n_67_, v_clauses_68_);
lean_dec_ref(v_clauses_68_);
lean_dec(v_n_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___redArg(lean_object* v_acc_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_acc_70_) == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_72_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__1_71_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_71_);
v_val_75_ = lean_ctor_get(v_acc_70_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v_acc_70_);
v___x_76_ = lean_apply_1(v_h__2_72_, v_val_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(lean_object* v_n_77_, lean_object* v_motive_78_, lean_object* v_acc_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_acc_79_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_81_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__1_80_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_80_);
v_val_84_ = lean_ctor_get(v_acc_79_, 0);
lean_inc(v_val_84_);
lean_dec_ref(v_acc_79_);
v___x_85_ = lean_apply_1(v_h__2_81_, v_val_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter___boxed(lean_object* v_n_86_, lean_object* v_motive_87_, lean_object* v_acc_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_folder_match__6_splitter(v_n_86_, v_motive_87_, v_acc_88_, v_h__1_89_, v_h__2_90_);
lean_dec(v_n_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object* v_cnf_96_){
_start:
{
lean_object* v_lifted_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_lratCnf_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_inc_ref(v_cnf_96_);
v_lifted_97_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(v_cnf_96_);
v___x_98_ = l_Std_Sat_CNF_numLiterals(v_cnf_96_);
lean_dec_ref(v_cnf_96_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v___x_98_, v___x_99_);
lean_dec(v___x_98_);
v_lratCnf_101_ = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(v___x_100_, v_lifted_97_);
lean_dec_ref(v_lifted_97_);
v___x_102_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT___closed__0));
v___x_103_ = l_Array_append___redArg(v___x_102_, v_lratCnf_101_);
lean_dec_ref(v_lratCnf_101_);
v___x_104_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(v___x_100_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_106_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__2_107_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_107_);
v_val_110_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_110_);
lean_dec_ref(v_x_105_);
v___x_111_ = lean_apply_1(v_h__1_106_, v_val_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(lean_object* v_n_112_, lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_115_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__2_116_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_116_);
v_val_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_val_119_);
lean_dec_ref(v_x_114_);
v___x_120_ = lean_apply_1(v_h__1_115_, v_val_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___boxed(lean_object* v_n_121_, lean_object* v_motive_122_, lean_object* v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(v_n_121_, v_motive_122_, v_x_123_, v_h__1_124_, v_h__2_125_);
lean_dec(v_n_121_);
return v_res_126_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
}
#ifdef __cplusplus
}
#endif
