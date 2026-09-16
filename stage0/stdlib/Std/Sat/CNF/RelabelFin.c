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
lean_dec_ref_known(v___x_48_, 1);
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
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_of_nat(v___x_101_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_arr_97_, v___x_103_, v___x_104_, v___x_99_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg___boxed(lean_object* v_arr_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_106_);
lean_dec_ref(v_arr_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(lean_object* v_arr_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_array_get_size(v_arr_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_nat_dec_eq(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_108_);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1___boxed(lean_object* v_arr_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(v_arr_115_);
lean_dec_ref(v_arr_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object* v_f_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_array_get_size(v_f_117_);
v___x_120_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_f_117_, v___x_118_, v___x_119_);
v___x_121_ = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(v___x_120_);
lean_dec_ref(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object* v_f_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Sat_CNF_maxLiteral(v_f_122_);
lean_dec_ref(v_f_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(lean_object* v_arr_124_, lean_object* v_h_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___boxed(lean_object* v_arr_127_, lean_object* v_h_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(v_arr_127_, v_h_128_);
lean_dec_ref(v_arr_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object* v_f_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_Sat_CNF_maxLiteral(v_f_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(0u);
return v___x_132_;
}
else
{
lean_object* v_val_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_val_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v___x_131_, 1);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_val_133_, v___x_134_);
lean_dec(v_val_133_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object* v_f_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Sat_CNF_numLiterals(v_f_136_);
lean_dec_ref(v_f_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_h__2_140_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_1(v_h__1_139_, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_144_; 
lean_dec(v_h__1_139_);
v_val_143_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v_x_138_, 1);
v___x_144_ = lean_apply_1(v_h__2_140_, v_val_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object* v_motive_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v_h__2_148_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_apply_1(v_h__1_147_, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v_val_151_; lean_object* v___x_152_; 
lean_dec(v_h__1_147_);
v_val_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v_x_146_, 1);
v___x_152_ = lean_apply_1(v_h__2_148_, v_val_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object* v_n_153_, lean_object* v_i_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_lt(v_i_154_, v_n_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
return v___x_156_;
}
else
{
lean_inc(v_i_154_);
return v_i_154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object* v_n_157_, lean_object* v_i_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Sat_CNF_relabelFin___lam__0(v_n_157_, v_i_158_);
lean_dec(v_i_158_);
lean_dec(v_n_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object* v_f_160_){
_start:
{
uint8_t v___x_161_; 
lean_inc_ref(v_f_160_);
v___x_161_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_array_get_size(v_f_160_);
lean_dec_ref(v_f_160_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_mk_array(v___x_162_, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v_n_165_; lean_object* v___f_166_; lean_object* v___x_167_; 
v_n_165_ = l_Std_Sat_CNF_numLiterals(v_f_160_);
v___f_166_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_relabelFin___lam__0___boxed), 2, 1);
lean_closure_set(v___f_166_, 0, v_n_165_);
v___x_167_ = l_Std_Sat_CNF_relabel___redArg(v___f_166_, v_f_160_);
return v___x_167_;
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
