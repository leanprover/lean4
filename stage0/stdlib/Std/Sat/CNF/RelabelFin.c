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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_fst_9_; lean_object* v___x_11_; 
v_fst_9_ = lean_ctor_get(v_head_4_, 0);
lean_inc(v_fst_9_);
lean_dec(v_head_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v_fst_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_fst_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_a_2_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_11_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_inc(v_x_15_);
return v_x_15_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; uint8_t v___x_19_; 
v_head_17_ = lean_ctor_get(v_x_16_, 0);
v_tail_18_ = lean_ctor_get(v_x_16_, 1);
v___x_19_ = lean_nat_dec_le(v_x_15_, v_head_17_);
if (v___x_19_ == 0)
{
v_x_16_ = v_tail_18_;
goto _start;
}
else
{
v_x_15_ = v_head_17_;
v_x_16_ = v_tail_18_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(v_x_22_, v_x_23_);
lean_dec(v_x_23_);
lean_dec(v_x_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
else
{
lean_object* v_head_27_; lean_object* v_tail_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_head_27_ = lean_ctor_get(v_x_25_, 0);
v_tail_28_ = lean_ctor_get(v_x_25_, 1);
v___x_29_ = l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(v_head_27_, v_tail_28_);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1___boxed(lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(v_x_31_);
lean_dec(v_x_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object* v_c_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v_c_33_, v___x_34_);
v___x_36_ = l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(v___x_35_);
lean_dec(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object* v_as_37_, size_t v_i_38_, size_t v_stop_39_, lean_object* v_b_40_){
_start:
{
lean_object* v___y_42_; uint8_t v___x_46_; 
v___x_46_ = lean_usize_dec_eq(v_i_38_, v_stop_39_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_array_uget_borrowed(v_as_37_, v_i_38_);
lean_inc(v___x_47_);
v___x_48_ = l_Std_Sat_CNF_Clause_maxLiteral(v___x_47_);
if (lean_obj_tag(v___x_48_) == 0)
{
v___y_42_ = v_b_40_;
goto v___jp_41_;
}
else
{
lean_object* v_val_49_; lean_object* v___x_50_; 
v_val_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_val_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_array_push(v_b_40_, v_val_49_);
v___y_42_ = v___x_50_;
goto v___jp_41_;
}
}
else
{
return v_b_40_;
}
v___jp_41_:
{
size_t v___x_43_; size_t v___x_44_; 
v___x_43_ = ((size_t)1ULL);
v___x_44_ = lean_usize_add(v_i_38_, v___x_43_);
v_i_38_ = v___x_44_;
v_b_40_ = v___y_42_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object* v_as_51_, lean_object* v_i_52_, lean_object* v_stop_53_, lean_object* v_b_54_){
_start:
{
size_t v_i_boxed_55_; size_t v_stop_boxed_56_; lean_object* v_res_57_; 
v_i_boxed_55_ = lean_unbox_usize(v_i_52_);
lean_dec(v_i_52_);
v_stop_boxed_56_ = lean_unbox_usize(v_stop_53_);
lean_dec(v_stop_53_);
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_51_, v_i_boxed_55_, v_stop_boxed_56_, v_b_54_);
lean_dec_ref(v_as_51_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object* v_as_60_, lean_object* v_start_61_, lean_object* v_stop_62_){
_start:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0));
v___x_64_ = lean_nat_dec_lt(v_start_61_, v_stop_62_);
if (v___x_64_ == 0)
{
return v___x_63_;
}
else
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_array_get_size(v_as_60_);
v___x_66_ = lean_nat_dec_le(v_stop_62_, v___x_65_);
if (v___x_66_ == 0)
{
uint8_t v___x_67_; 
v___x_67_ = lean_nat_dec_lt(v_start_61_, v___x_65_);
if (v___x_67_ == 0)
{
return v___x_63_;
}
else
{
size_t v___x_68_; size_t v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_usize_of_nat(v_start_61_);
v___x_69_ = lean_usize_of_nat(v___x_65_);
v___x_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_60_, v___x_68_, v___x_69_, v___x_63_);
return v___x_70_;
}
}
else
{
size_t v___x_71_; size_t v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_usize_of_nat(v_start_61_);
v___x_72_ = lean_usize_of_nat(v_stop_62_);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_60_, v___x_71_, v___x_72_, v___x_63_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object* v_as_74_, lean_object* v_start_75_, lean_object* v_stop_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_as_74_, v_start_75_, v_stop_76_);
lean_dec(v_stop_76_);
lean_dec(v_start_75_);
lean_dec_ref(v_as_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(lean_object* v_as_78_, size_t v_i_79_, size_t v_stop_80_, lean_object* v_b_81_){
_start:
{
lean_object* v___y_83_; uint8_t v___x_87_; 
v___x_87_ = lean_usize_dec_eq(v_i_79_, v_stop_80_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = lean_array_uget_borrowed(v_as_78_, v_i_79_);
v___x_89_ = lean_nat_dec_le(v_b_81_, v___x_88_);
if (v___x_89_ == 0)
{
v___y_83_ = v_b_81_;
goto v___jp_82_;
}
else
{
v___y_83_ = v___x_88_;
goto v___jp_82_;
}
}
else
{
lean_inc(v_b_81_);
return v_b_81_;
}
v___jp_82_:
{
size_t v___x_84_; size_t v___x_85_; 
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_add(v_i_79_, v___x_84_);
v_i_79_ = v___x_85_;
v_b_81_ = v___y_83_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3___boxed(lean_object* v_as_90_, lean_object* v_i_91_, lean_object* v_stop_92_, lean_object* v_b_93_){
_start:
{
size_t v_i_boxed_94_; size_t v_stop_boxed_95_; lean_object* v_res_96_; 
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_stop_boxed_95_ = lean_unbox_usize(v_stop_92_);
lean_dec(v_stop_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_as_90_, v_i_boxed_94_, v_stop_boxed_95_, v_b_93_);
lean_dec(v_b_93_);
lean_dec_ref(v_as_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(lean_object* v_arr_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_array_fget_borrowed(v_arr_97_, v___x_98_);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_array_get_size(v_arr_97_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_inc(v___x_99_);
return v___x_99_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_103_ == 0)
{
if (v___x_102_ == 0)
{
lean_inc(v___x_99_);
return v___x_99_;
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_of_nat(v___x_101_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_arr_97_, v___x_104_, v___x_105_, v___x_99_);
return v___x_106_;
}
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_arr_97_, v___x_107_, v___x_108_, v___x_99_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg___boxed(lean_object* v_arr_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_110_);
lean_dec_ref(v_arr_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(lean_object* v_arr_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_array_get_size(v_arr_112_);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_nat_dec_eq(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_112_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1___boxed(lean_object* v_arr_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(v_arr_119_);
lean_dec_ref(v_arr_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object* v_f_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_array_get_size(v_f_121_);
v___x_124_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_f_121_, v___x_122_, v___x_123_);
v___x_125_ = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(v___x_124_);
lean_dec_ref(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object* v_f_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Sat_CNF_maxLiteral(v_f_126_);
lean_dec_ref(v_f_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(lean_object* v_arr_128_, lean_object* v_h_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___boxed(lean_object* v_arr_131_, lean_object* v_h_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(v_arr_131_, v_h_132_);
lean_dec_ref(v_arr_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object* v_f_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_Sat_CNF_maxLiteral(v_f_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(0u);
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_val_137_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v___x_135_);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_val_137_, v___x_138_);
lean_dec(v_val_137_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object* v_f_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_Sat_CNF_numLiterals(v_f_140_);
lean_dec_ref(v_f_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_144_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_1(v_h__1_143_, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v_val_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v_val_147_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_val_147_);
lean_dec_ref(v_x_142_);
v___x_148_ = lean_apply_1(v_h__2_144_, v_val_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_h__2_152_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_apply_1(v_h__1_151_, v___x_153_);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_151_);
v_val_155_ = lean_ctor_get(v_x_150_, 0);
lean_inc(v_val_155_);
lean_dec_ref(v_x_150_);
v___x_156_ = lean_apply_1(v_h__2_152_, v_val_155_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object* v_n_157_, lean_object* v_i_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_lt(v_i_158_, v_n_157_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_unsigned_to_nat(0u);
return v___x_160_;
}
else
{
lean_inc(v_i_158_);
return v_i_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object* v_n_161_, lean_object* v_i_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Sat_CNF_relabelFin___lam__0(v_n_161_, v_i_162_);
lean_dec(v_i_162_);
lean_dec(v_n_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object* v_f_164_){
_start:
{
uint8_t v___x_165_; 
lean_inc_ref(v_f_164_);
v___x_165_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_array_get_size(v_f_164_);
lean_dec_ref(v_f_164_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_mk_array(v___x_166_, v___x_167_);
return v___x_168_;
}
else
{
lean_object* v_n_169_; lean_object* v___f_170_; lean_object* v___x_171_; 
v_n_169_ = l_Std_Sat_CNF_numLiterals(v_f_164_);
v___f_170_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_relabelFin___lam__0___boxed), 2, 1);
lean_closure_set(v___f_170_, 0, v_n_169_);
v___x_171_ = l_Std_Sat_CNF_relabel___redArg(v___f_170_, v_f_164_);
return v___x_171_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
