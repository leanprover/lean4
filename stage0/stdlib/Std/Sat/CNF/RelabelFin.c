// Lean compiler output
// Module: Std.Sat.CNF.RelabelFin
// Imports: public import Init.Data.Nat.Order public import Std.Sat.CNF.Relabel import Init.Data.Option.Lemmas import Init.Omega import Init.Data.List.Impl import Init.Data.List.MinMax public import Init.Data.Array.MinMax import Init.TacticsExtra
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_CNF_relabelFin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_relabelFin___closed__0;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___y_6_; uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_12_ = lean_nat_dec_le(v_b_4_, v___x_11_);
if (v___x_12_ == 0)
{
v___y_6_ = v_b_4_;
goto v___jp_5_;
}
else
{
v___y_6_ = v___x_11_;
goto v___jp_5_;
}
}
else
{
lean_inc(v_b_4_);
return v_b_4_;
}
v___jp_5_:
{
size_t v___x_7_; size_t v___x_8_; 
v___x_7_ = ((size_t)1ULL);
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
v_b_4_ = v___y_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1___boxed(lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_, lean_object* v_b_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; lean_object* v_res_19_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(v_as_13_, v_i_boxed_17_, v_stop_boxed_18_, v_b_16_);
lean_dec(v_b_16_);
lean_dec_ref(v_as_13_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(lean_object* v_arr_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_array_fget_borrowed(v_arr_20_, v___x_21_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_array_get_size(v_arr_20_);
v___x_25_ = lean_nat_dec_lt(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_inc(v___x_22_);
return v___x_22_;
}
else
{
size_t v___x_26_; size_t v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_of_nat(v___x_24_);
v___x_28_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(v_arr_20_, v___x_26_, v___x_27_, v___x_22_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg___boxed(lean_object* v_arr_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(v_arr_29_);
lean_dec_ref(v_arr_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object* v_arr_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_32_ = lean_array_get_size(v_arr_31_);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_nat_dec_eq(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(v_arr_31_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0___boxed(lean_object* v_arr_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v_arr_38_);
lean_dec_ref(v_arr_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object* v_c_40_){
_start:
{
lean_object* v_atoms_41_; lean_object* v___x_42_; 
v_atoms_41_ = lean_ctor_get(v_c_40_, 0);
v___x_42_ = l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v_atoms_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral___boxed(lean_object* v_c_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Sat_CNF_Clause_maxLiteral(v_c_43_);
lean_dec_ref(v_c_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0(lean_object* v_arr_45_, lean_object* v_h_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(v_arr_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___boxed(lean_object* v_arr_48_, lean_object* v_h_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0(v_arr_48_, v_h_49_);
lean_dec_ref(v_arr_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object* v_as_51_, size_t v_i_52_, size_t v_stop_53_, lean_object* v_b_54_){
_start:
{
lean_object* v___y_56_; uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_eq(v_i_52_, v_stop_53_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_array_uget_borrowed(v_as_51_, v_i_52_);
v___x_62_ = l_Std_Sat_CNF_Clause_maxLiteral(v___x_61_);
if (lean_obj_tag(v___x_62_) == 0)
{
v___y_56_ = v_b_54_;
goto v___jp_55_;
}
else
{
lean_object* v_val_63_; lean_object* v___x_64_; 
v_val_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v___x_62_, 1);
v___x_64_ = lean_array_push(v_b_54_, v_val_63_);
v___y_56_ = v___x_64_;
goto v___jp_55_;
}
}
else
{
return v_b_54_;
}
v___jp_55_:
{
size_t v___x_57_; size_t v___x_58_; 
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_add(v_i_52_, v___x_57_);
v_i_52_ = v___x_58_;
v_b_54_ = v___y_56_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v_b_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; lean_object* v_res_71_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_65_, v_i_boxed_69_, v_stop_boxed_70_, v_b_68_);
lean_dec_ref(v_as_65_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object* v_as_74_, lean_object* v_start_75_, lean_object* v_stop_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0));
v___x_78_ = lean_nat_dec_lt(v_start_75_, v_stop_76_);
if (v___x_78_ == 0)
{
return v___x_77_;
}
else
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_array_get_size(v_as_74_);
v___x_80_ = lean_nat_dec_le(v_stop_76_, v___x_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = lean_nat_dec_lt(v_start_75_, v___x_79_);
if (v___x_81_ == 0)
{
return v___x_77_;
}
else
{
size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_usize_of_nat(v_start_75_);
v___x_83_ = lean_usize_of_nat(v___x_79_);
v___x_84_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_74_, v___x_82_, v___x_83_, v___x_77_);
return v___x_84_;
}
}
else
{
size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_usize_of_nat(v_start_75_);
v___x_86_ = lean_usize_of_nat(v_stop_76_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_74_, v___x_85_, v___x_86_, v___x_77_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object* v_as_88_, lean_object* v_start_89_, lean_object* v_stop_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_as_88_, v_start_89_, v_stop_90_);
lean_dec(v_stop_90_);
lean_dec(v_start_89_);
lean_dec_ref(v_as_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object* v_f_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v_f_92_);
v___x_95_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_f_92_, v___x_93_, v___x_94_);
v___x_96_ = l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v___x_95_);
lean_dec_ref(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object* v_f_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_Sat_CNF_maxLiteral(v_f_97_);
lean_dec_ref(v_f_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object* v_f_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Sat_CNF_maxLiteral(v_f_99_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_unsigned_to_nat(0u);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_val_102_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_102_);
lean_dec_ref_known(v___x_100_, 1);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_val_102_, v___x_103_);
lean_dec(v_val_102_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object* v_f_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Sat_CNF_numLiterals(v_f_105_);
lean_dec_ref(v_f_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_109_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_1(v_h__1_108_, v___x_110_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v___x_113_; 
lean_dec(v_h__1_108_);
v_val_112_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v_x_107_, 1);
v___x_113_ = lean_apply_1(v_h__2_109_, v_val_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object* v_motive_114_, lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_h__2_117_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_1(v_h__1_116_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; lean_object* v___x_121_; 
lean_dec(v_h__1_116_);
v_val_120_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_x_115_, 1);
v___x_121_ = lean_apply_1(v_h__2_117_, v_val_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object* v_n_122_, lean_object* v_i_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_lt(v_i_123_, v_n_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(0u);
return v___x_125_;
}
else
{
lean_inc(v_i_123_);
return v_i_123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object* v_n_126_, lean_object* v_i_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Sat_CNF_relabelFin___lam__0(v_n_126_, v_i_127_);
lean_dec(v_i_127_);
lean_dec(v_n_126_);
return v_res_128_;
}
}
static lean_object* _init_l_Std_Sat_CNF_relabelFin___closed__0(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = l_ByteArray_empty;
v___x_130_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0));
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object* v_f_132_){
_start:
{
uint8_t v___x_133_; 
lean_inc_ref(v_f_132_);
v___x_133_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_array_get_size(v_f_132_);
lean_dec_ref(v_f_132_);
v___x_135_ = lean_obj_once(&l_Std_Sat_CNF_relabelFin___closed__0, &l_Std_Sat_CNF_relabelFin___closed__0_once, _init_l_Std_Sat_CNF_relabelFin___closed__0);
v___x_136_ = lean_mk_array(v___x_134_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_n_137_; lean_object* v___f_138_; lean_object* v___x_139_; 
v_n_137_ = l_Std_Sat_CNF_numLiterals(v_f_132_);
v___f_138_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_relabelFin___lam__0___boxed), 2, 1);
lean_closure_set(v___f_138_, 0, v_n_137_);
v___x_139_ = l_Std_Sat_CNF_relabel___redArg(v___f_138_, v_f_132_);
return v___x_139_;
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MinMax(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_RelabelFin(builtin);
}
#ifdef __cplusplus
}
#endif
