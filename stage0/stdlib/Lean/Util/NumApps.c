// Lean compiler output
// Module: Lean.Util.NumApps
// Imports: public import Lean.Expr public import Lean.Util.PtrSet
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
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_NumApps_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumApps_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_NumApps_main___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumApps_main___closed__0;
static lean_once_cell_t l_Lean_Expr_NumApps_main___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_NumApps_main___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_main(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Expr_numApps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_numApps___closed__0 = (const lean_object*)&l_Lean_Expr_numApps___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_numApps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_numApps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_key_3_; lean_object* v_value_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_31_; 
v_key_3_ = lean_ctor_get(v_x_2_, 0);
v_value_4_ = lean_ctor_get(v_x_2_, 1);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_31_ == 0)
{
v___x_7_ = v_x_2_;
v_isShared_8_ = v_isSharedCheck_31_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_value_4_);
lean_inc(v_key_3_);
lean_dec(v_x_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_31_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; size_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v___x_13_; uint64_t v___x_14_; uint64_t v___x_15_; uint64_t v_fold_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; size_t v___x_20_; size_t v___x_21_; size_t v___x_22_; size_t v___x_23_; size_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_9_ = lean_array_get_size(v_x_1_);
v___x_10_ = lean_ptr_addr(v_key_3_);
v___x_11_ = lean_usize_to_uint64(v___x_10_);
v___x_12_ = 11ULL;
v___x_13_ = lean_uint64_mix_hash(v___x_11_, v___x_12_);
v___x_14_ = 32ULL;
v___x_15_ = lean_uint64_shift_right(v___x_13_, v___x_14_);
v_fold_16_ = lean_uint64_xor(v___x_13_, v___x_15_);
v___x_17_ = 16ULL;
v___x_18_ = lean_uint64_shift_right(v_fold_16_, v___x_17_);
v___x_19_ = lean_uint64_xor(v_fold_16_, v___x_18_);
v___x_20_ = lean_uint64_to_usize(v___x_19_);
v___x_21_ = lean_usize_of_nat(v___x_9_);
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_sub(v___x_21_, v___x_22_);
v___x_24_ = lean_usize_land(v___x_20_, v___x_23_);
v___x_25_ = lean_array_uget_borrowed(v_x_1_, v___x_24_);
lean_inc(v___x_25_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v___x_25_);
v___x_27_ = v___x_7_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_key_3_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_value_4_);
lean_ctor_set(v_reuseFailAlloc_30_, 2, v___x_25_);
v___x_27_ = v_reuseFailAlloc_30_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_array_uset(v_x_1_, v___x_24_, v___x_27_);
v_x_1_ = v___x_28_;
v_x_2_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(lean_object* v_i_32_, lean_object* v_source_33_, lean_object* v_target_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_array_get_size(v_source_33_);
v___x_36_ = lean_nat_dec_lt(v_i_32_, v___x_35_);
if (v___x_36_ == 0)
{
lean_dec_ref(v_source_33_);
lean_dec(v_i_32_);
return v_target_34_;
}
else
{
lean_object* v_es_37_; lean_object* v___x_38_; lean_object* v_source_39_; lean_object* v_target_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_es_37_ = lean_array_fget(v_source_33_, v_i_32_);
v___x_38_ = lean_box(0);
v_source_39_ = lean_array_fset(v_source_33_, v_i_32_, v___x_38_);
v_target_40_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_34_, v_es_37_);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_i_32_, v___x_41_);
lean_dec(v_i_32_);
v_i_32_ = v___x_42_;
v_source_33_ = v_source_39_;
v_target_34_ = v_target_40_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(lean_object* v_data_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_nbuckets_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_45_ = lean_array_get_size(v_data_44_);
v___x_46_ = lean_unsigned_to_nat(2u);
v_nbuckets_47_ = lean_nat_mul(v___x_45_, v___x_46_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_box(0);
v___x_50_ = lean_mk_array(v_nbuckets_47_, v___x_49_);
v___x_51_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v___x_48_, v_data_44_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(lean_object* v_a_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
else
{
lean_object* v_key_55_; lean_object* v_tail_56_; size_t v___x_57_; size_t v___x_58_; uint8_t v___x_59_; 
v_key_55_ = lean_ctor_get(v_x_53_, 0);
v_tail_56_ = lean_ctor_get(v_x_53_, 2);
v___x_57_ = lean_ptr_addr(v_key_55_);
v___x_58_ = lean_ptr_addr(v_a_52_);
v___x_59_ = lean_usize_dec_eq(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
v_x_53_ = v_tail_56_;
goto _start;
}
else
{
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_61_, v_x_62_);
lean_dec(v_x_62_);
lean_dec_ref(v_a_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(lean_object* v_m_65_, lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
lean_object* v_size_68_; lean_object* v_buckets_69_; lean_object* v___x_70_; size_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v_fold_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v_bkt_86_; uint8_t v___x_87_; 
v_size_68_ = lean_ctor_get(v_m_65_, 0);
v_buckets_69_ = lean_ctor_get(v_m_65_, 1);
v___x_70_ = lean_array_get_size(v_buckets_69_);
v___x_71_ = lean_ptr_addr(v_a_66_);
v___x_72_ = lean_usize_to_uint64(v___x_71_);
v___x_73_ = 11ULL;
v___x_74_ = lean_uint64_mix_hash(v___x_72_, v___x_73_);
v___x_75_ = 32ULL;
v___x_76_ = lean_uint64_shift_right(v___x_74_, v___x_75_);
v_fold_77_ = lean_uint64_xor(v___x_74_, v___x_76_);
v___x_78_ = 16ULL;
v___x_79_ = lean_uint64_shift_right(v_fold_77_, v___x_78_);
v___x_80_ = lean_uint64_xor(v_fold_77_, v___x_79_);
v___x_81_ = lean_uint64_to_usize(v___x_80_);
v___x_82_ = lean_usize_of_nat(v___x_70_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_sub(v___x_82_, v___x_83_);
v___x_85_ = lean_usize_land(v___x_81_, v___x_84_);
v_bkt_86_ = lean_array_uget_borrowed(v_buckets_69_, v___x_85_);
v___x_87_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_66_, v_bkt_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_108_; 
lean_inc_ref(v_buckets_69_);
lean_inc(v_size_68_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_m_65_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; lean_object* v_unused_110_; 
v_unused_109_ = lean_ctor_get(v_m_65_, 1);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_m_65_, 0);
lean_dec(v_unused_110_);
v___x_89_ = v_m_65_;
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_m_65_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v_size_x27_92_; lean_object* v___x_93_; lean_object* v_buckets_x27_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v_size_x27_92_ = lean_nat_add(v_size_68_, v___x_91_);
lean_dec(v_size_68_);
lean_inc(v_bkt_86_);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v_a_66_);
lean_ctor_set(v___x_93_, 1, v_b_67_);
lean_ctor_set(v___x_93_, 2, v_bkt_86_);
v_buckets_x27_94_ = lean_array_uset(v_buckets_69_, v___x_85_, v___x_93_);
v___x_95_ = lean_unsigned_to_nat(4u);
v___x_96_ = lean_nat_mul(v_size_x27_92_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(3u);
v___x_98_ = lean_nat_div(v___x_96_, v___x_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_array_get_size(v_buckets_x27_94_);
v___x_100_ = lean_nat_dec_le(v___x_98_, v___x_99_);
lean_dec(v___x_98_);
if (v___x_100_ == 0)
{
lean_object* v_val_101_; lean_object* v___x_103_; 
v_val_101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_buckets_x27_94_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_val_101_);
lean_ctor_set(v___x_89_, 0, v_size_x27_92_);
v___x_103_ = v___x_89_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_size_x27_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_val_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
lean_object* v___x_106_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_buckets_x27_94_);
lean_ctor_set(v___x_89_, 0, v_size_x27_92_);
v___x_106_ = v___x_89_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_size_x27_92_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_buckets_x27_94_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_dec(v_b_67_);
lean_dec_ref(v_a_66_);
return v_m_65_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(lean_object* v_m_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_buckets_113_; lean_object* v___x_114_; size_t v___x_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v_fold_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_buckets_113_ = lean_ctor_get(v_m_111_, 1);
v___x_114_ = lean_array_get_size(v_buckets_113_);
v___x_115_ = lean_ptr_addr(v_a_112_);
v___x_116_ = lean_usize_to_uint64(v___x_115_);
v___x_117_ = 11ULL;
v___x_118_ = lean_uint64_mix_hash(v___x_116_, v___x_117_);
v___x_119_ = 32ULL;
v___x_120_ = lean_uint64_shift_right(v___x_118_, v___x_119_);
v_fold_121_ = lean_uint64_xor(v___x_118_, v___x_120_);
v___x_122_ = 16ULL;
v___x_123_ = lean_uint64_shift_right(v_fold_121_, v___x_122_);
v___x_124_ = lean_uint64_xor(v_fold_121_, v___x_123_);
v___x_125_ = lean_uint64_to_usize(v___x_124_);
v___x_126_ = lean_usize_of_nat(v___x_114_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_sub(v___x_126_, v___x_127_);
v___x_129_ = lean_usize_land(v___x_125_, v___x_128_);
v___x_130_ = lean_array_uget_borrowed(v_buckets_113_, v___x_129_);
v___x_131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_112_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(lean_object* v_m_132_, lean_object* v_a_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_132_, v_a_133_);
lean_dec_ref(v_a_133_);
lean_dec_ref(v_m_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_visit___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v_dummy_137_; 
v___x_136_ = lean_box(0);
v_dummy_137_ = l_Lean_Expr_sort___override(v___x_136_);
return v_dummy_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(lean_object* v_x_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___y_143_; 
if (lean_obj_tag(v_x_138_) == 5)
{
lean_object* v_fn_168_; lean_object* v_arg_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_fn_168_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_fn_168_);
v_arg_169_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_arg_169_);
lean_dec_ref(v_x_138_);
v___x_170_ = lean_array_set(v_x_139_, v_x_140_, v_arg_169_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_sub(v_x_140_, v___x_171_);
lean_dec(v_x_140_);
v_x_138_ = v_fn_168_;
v_x_139_ = v___x_170_;
v_x_140_ = v___x_172_;
goto _start;
}
else
{
lean_dec(v_x_140_);
if (lean_obj_tag(v_x_138_) == 4)
{
lean_object* v_declName_174_; lean_object* v_visited_175_; lean_object* v_counters_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_191_; 
v_declName_174_ = lean_ctor_get(v_x_138_, 0);
v_visited_175_ = lean_ctor_get(v___y_141_, 0);
v_counters_176_ = lean_ctor_get(v___y_141_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v___y_141_);
if (v_isSharedCheck_191_ == 0)
{
v___x_178_ = v___y_141_;
v_isShared_179_ = v_isSharedCheck_191_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_counters_176_);
lean_inc(v_visited_175_);
lean_dec(v___y_141_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_191_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___y_181_; lean_object* v___x_188_; 
v___x_188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_counters_176_, v_declName_174_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___y_181_ = v___x_189_;
goto v___jp_180_;
}
else
{
lean_object* v_val_190_; 
v_val_190_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_val_190_);
lean_dec_ref(v___x_188_);
v___y_181_ = v_val_190_;
goto v___jp_180_;
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v___y_181_, v___x_182_);
lean_dec(v___y_181_);
lean_inc(v_declName_174_);
v___x_184_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_174_, v___x_183_, v_counters_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_184_);
v___x_186_ = v___x_178_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_visited_175_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v___y_143_ = v___x_186_;
goto v___jp_142_;
}
}
}
}
else
{
v___y_143_ = v___y_141_;
goto v___jp_142_;
}
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v_snd_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_166_; 
v___x_144_ = l_Lean_Expr_NumApps_visit(v_x_138_, v___y_143_);
v_snd_145_ = lean_ctor_get(v___x_144_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v___x_144_, 0);
lean_dec(v_unused_167_);
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_166_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_snd_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_166_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_array_get_size(v_x_139_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_nat_dec_lt(v___x_149_, v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v___x_154_; 
lean_dec_ref(v_x_139_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_151_);
v___x_154_ = v___x_147_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_snd_145_);
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
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_le(v___x_150_, v___x_150_);
if (v___x_156_ == 0)
{
if (v___x_152_ == 0)
{
lean_object* v___x_158_; 
lean_dec_ref(v_x_139_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_151_);
v___x_158_ = v___x_147_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_snd_145_);
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
size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
lean_del_object(v___x_147_);
v___x_160_ = ((size_t)0ULL);
v___x_161_ = lean_usize_of_nat(v___x_150_);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_139_, v___x_160_, v___x_161_, v___x_151_, v_snd_145_);
lean_dec_ref(v_x_139_);
return v___x_162_;
}
}
else
{
size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; 
lean_del_object(v___x_147_);
v___x_163_ = ((size_t)0ULL);
v___x_164_ = lean_usize_of_nat(v___x_150_);
v___x_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_139_, v___x_163_, v___x_164_, v___x_151_, v_snd_145_);
lean_dec_ref(v_x_139_);
return v___x_165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object* v_e_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_d_195_; lean_object* v_b_196_; lean_object* v___y_197_; lean_object* v_visited_201_; lean_object* v_counters_202_; uint8_t v___x_203_; 
v_visited_201_ = lean_ctor_get(v_a_193_, 0);
v_counters_202_ = lean_ctor_get(v_a_193_, 1);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_visited_201_, v_e_192_);
if (v___x_203_ == 0)
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_235_; 
lean_inc(v_counters_202_);
lean_inc_ref(v_visited_201_);
v_isSharedCheck_235_ = !lean_is_exclusive(v_a_193_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; lean_object* v_unused_237_; 
v_unused_236_ = lean_ctor_get(v_a_193_, 1);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_a_193_, 0);
lean_dec(v_unused_237_);
v___x_205_ = v_a_193_;
v_isShared_206_ = v_isSharedCheck_235_;
goto v_resetjp_204_;
}
else
{
lean_dec(v_a_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_235_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_207_ = lean_box(0);
lean_inc_ref(v_e_192_);
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_visited_201_, v_e_192_, v___x_207_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_counters_202_);
v___x_210_ = v_reuseFailAlloc_234_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
switch(lean_obj_tag(v_e_192_))
{
case 7:
{
lean_object* v_binderType_211_; lean_object* v_body_212_; 
v_binderType_211_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_binderType_211_);
v_body_212_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_body_212_);
lean_dec_ref(v_e_192_);
v_d_195_ = v_binderType_211_;
v_b_196_ = v_body_212_;
v___y_197_ = v___x_210_;
goto v___jp_194_;
}
case 6:
{
lean_object* v_binderType_213_; lean_object* v_body_214_; 
v_binderType_213_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_binderType_213_);
v_body_214_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_body_214_);
lean_dec_ref(v_e_192_);
v_d_195_ = v_binderType_213_;
v_b_196_ = v_body_214_;
v___y_197_ = v___x_210_;
goto v___jp_194_;
}
case 10:
{
lean_object* v_expr_215_; 
v_expr_215_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_expr_215_);
lean_dec_ref(v_e_192_);
v_e_192_ = v_expr_215_;
v_a_193_ = v___x_210_;
goto _start;
}
case 8:
{
lean_object* v_type_217_; lean_object* v_value_218_; lean_object* v_body_219_; lean_object* v___x_220_; lean_object* v_snd_221_; lean_object* v___x_222_; lean_object* v_snd_223_; 
v_type_217_ = lean_ctor_get(v_e_192_, 1);
lean_inc_ref(v_type_217_);
v_value_218_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_value_218_);
v_body_219_ = lean_ctor_get(v_e_192_, 3);
lean_inc_ref(v_body_219_);
lean_dec_ref(v_e_192_);
v___x_220_ = l_Lean_Expr_NumApps_visit(v_type_217_, v___x_210_);
v_snd_221_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_snd_221_);
lean_dec_ref(v___x_220_);
v___x_222_ = l_Lean_Expr_NumApps_visit(v_value_218_, v_snd_221_);
v_snd_223_ = lean_ctor_get(v___x_222_, 1);
lean_inc(v_snd_223_);
lean_dec_ref(v___x_222_);
v_e_192_ = v_body_219_;
v_a_193_ = v_snd_223_;
goto _start;
}
case 5:
{
lean_object* v_dummy_225_; lean_object* v_nargs_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_dummy_225_ = lean_obj_once(&l_Lean_Expr_NumApps_visit___closed__0, &l_Lean_Expr_NumApps_visit___closed__0_once, _init_l_Lean_Expr_NumApps_visit___closed__0);
v_nargs_226_ = l_Lean_Expr_getAppNumArgs(v_e_192_);
lean_inc(v_nargs_226_);
v___x_227_ = lean_mk_array(v_nargs_226_, v_dummy_225_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_sub(v_nargs_226_, v___x_228_);
lean_dec(v_nargs_226_);
v___x_230_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(v_e_192_, v___x_227_, v___x_229_, v___x_210_);
return v___x_230_;
}
case 11:
{
lean_object* v_struct_231_; 
v_struct_231_ = lean_ctor_get(v_e_192_, 2);
lean_inc_ref(v_struct_231_);
lean_dec_ref(v_e_192_);
v_e_192_ = v_struct_231_;
v_a_193_ = v___x_210_;
goto _start;
}
default: 
{
lean_object* v___x_233_; 
lean_dec_ref(v_e_192_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_207_);
lean_ctor_set(v___x_233_, 1, v___x_210_);
return v___x_233_;
}
}
}
}
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_e_192_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v_a_193_);
return v___x_239_;
}
v___jp_194_:
{
lean_object* v___x_198_; lean_object* v_snd_199_; 
v___x_198_ = l_Lean_Expr_NumApps_visit(v_d_195_, v___y_197_);
v_snd_199_ = lean_ctor_get(v___x_198_, 1);
lean_inc(v_snd_199_);
lean_dec_ref(v___x_198_);
v_e_192_ = v_b_196_;
v_a_193_ = v_snd_199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object* v_as_240_, size_t v_i_241_, size_t v_stop_242_, lean_object* v_b_243_, lean_object* v___y_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_eq(v_i_241_, v_stop_242_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_fst_248_; lean_object* v_snd_249_; size_t v___x_250_; size_t v___x_251_; 
v___x_246_ = lean_array_uget_borrowed(v_as_240_, v_i_241_);
lean_inc(v___x_246_);
v___x_247_ = l_Lean_Expr_NumApps_visit(v___x_246_, v___y_244_);
v_fst_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_fst_248_);
v_snd_249_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_snd_249_);
lean_dec_ref(v___x_247_);
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_241_, v___x_250_);
v_i_241_ = v___x_251_;
v_b_243_ = v_fst_248_;
v___y_244_ = v_snd_249_;
goto _start;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_b_243_);
lean_ctor_set(v___x_253_, 1, v___y_244_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object* v_as_254_, lean_object* v_i_255_, lean_object* v_stop_256_, lean_object* v_b_257_, lean_object* v___y_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_256_);
lean_dec(v_stop_256_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_254_, v_i_boxed_259_, v_stop_boxed_260_, v_b_257_, v___y_258_);
lean_dec_ref(v_as_254_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object* v_00_u03b2_262_, lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_263_, v_a_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(v_00_u03b2_266_, v_m_267_, v_a_268_);
lean_dec_ref(v_a_268_);
lean_dec_ref(v_m_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2(lean_object* v_00_u03b2_271_, lean_object* v_m_272_, lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_m_272_, v_a_273_, v_b_274_);
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object* v_00_u03b2_276_, lean_object* v_a_277_, lean_object* v_x_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_277_, v_x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_280_, lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(v_00_u03b2_280_, v_a_281_, v_x_282_);
lean_dec(v_x_282_);
lean_dec_ref(v_a_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3(lean_object* v_00_u03b2_285_, lean_object* v_data_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_data_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_288_, lean_object* v_i_289_, lean_object* v_source_290_, lean_object* v_target_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v_i_289_, v_source_290_, v_target_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_294_, v_x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__0(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(64u);
v___x_298_ = l_Lean_mkPtrSet___redArg(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(1);
v___x_300_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__0, &l_Lean_Expr_NumApps_main___closed__0_once, _init_l_Lean_Expr_NumApps_main___closed__0);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_main(lean_object* v_e_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_snd_305_; lean_object* v_counters_306_; 
v___x_303_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__1, &l_Lean_Expr_NumApps_main___closed__1_once, _init_l_Lean_Expr_NumApps_main___closed__1);
v___x_304_ = l_Lean_Expr_NumApps_visit(v_e_302_, v___x_303_);
v_snd_305_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_snd_305_);
lean_dec_ref(v___x_304_);
v_counters_306_ = lean_ctor_get(v_snd_305_, 1);
lean_inc(v_counters_306_);
lean_dec(v_snd_305_);
return v_counters_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(lean_object* v_e_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Expr_NumApps_main(v_e_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(lean_object* v_threshold_309_, lean_object* v_init_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_d_314_; 
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v_l_319_; lean_object* v_r_320_; lean_object* v___x_321_; lean_object* v_a_322_; 
v_k_317_ = lean_ctor_get(v_x_311_, 1);
v_v_318_ = lean_ctor_get(v_x_311_, 2);
v_l_319_ = lean_ctor_get(v_x_311_, 3);
v_r_320_ = lean_ctor_get(v_x_311_, 4);
v___x_321_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_309_, v_init_310_, v_l_319_);
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
if (lean_obj_tag(v_a_322_) == 0)
{
lean_object* v_a_323_; 
lean_dec_ref(v___x_321_);
v_a_323_ = lean_ctor_get(v_a_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v_a_322_);
v_d_314_ = v_a_323_;
goto v___jp_313_;
}
else
{
lean_object* v_a_324_; uint8_t v___x_325_; 
v_a_324_ = lean_ctor_get(v_a_322_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v_a_322_);
v___x_325_ = lean_nat_dec_lt(v_threshold_309_, v_v_318_);
if (v___x_325_ == 0)
{
lean_object* v_a_326_; 
lean_dec(v_a_324_);
v_a_326_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_321_);
if (lean_obj_tag(v_a_326_) == 0)
{
lean_object* v_a_327_; 
v_a_327_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v_a_326_);
v_d_314_ = v_a_327_;
goto v___jp_313_;
}
else
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v_a_326_, 0);
lean_inc(v_a_328_);
lean_dec_ref(v_a_326_);
v_init_310_ = v_a_328_;
v_x_311_ = v_r_320_;
goto _start;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v___x_321_);
lean_inc(v_v_318_);
lean_inc(v_k_317_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_k_317_);
lean_ctor_set(v___x_330_, 1, v_v_318_);
v___x_331_ = lean_array_push(v_a_324_, v___x_330_);
v_init_310_ = v___x_331_;
v_x_311_ = v_r_320_;
goto _start;
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_init_310_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_d_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(lean_object* v_threshold_335_, lean_object* v_init_336_, lean_object* v_x_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_335_, v_init_336_, v_x_337_);
lean_dec(v_x_337_);
lean_dec(v_threshold_335_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(lean_object* v_hi_340_, lean_object* v_pivot_341_, lean_object* v_as_342_, lean_object* v_i_343_, lean_object* v_k_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = lean_nat_dec_lt(v_k_344_, v_hi_340_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_k_344_);
v___x_346_ = lean_array_fswap(v_as_342_, v_i_343_, v_hi_340_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_i_343_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v_snd_348_; lean_object* v___x_349_; lean_object* v_snd_350_; uint8_t v___x_351_; 
v_snd_348_ = lean_ctor_get(v_pivot_341_, 1);
v___x_349_ = lean_array_fget_borrowed(v_as_342_, v_k_344_);
v_snd_350_ = lean_ctor_get(v___x_349_, 1);
v___x_351_ = lean_nat_dec_lt(v_snd_348_, v_snd_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_k_344_, v___x_352_);
lean_dec(v_k_344_);
v_k_344_ = v___x_353_;
goto _start;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_array_fswap(v_as_342_, v_i_343_, v_k_344_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_i_343_, v___x_356_);
lean_dec(v_i_343_);
v___x_358_ = lean_nat_add(v_k_344_, v___x_356_);
lean_dec(v_k_344_);
v_as_342_ = v___x_355_;
v_i_343_ = v___x_357_;
v_k_344_ = v___x_358_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_360_, lean_object* v_pivot_361_, lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_k_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_360_, v_pivot_361_, v_as_362_, v_i_363_, v_k_364_);
lean_dec_ref(v_pivot_361_);
lean_dec(v_hi_360_);
return v_res_365_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
lean_object* v_snd_368_; lean_object* v_snd_369_; uint8_t v___x_370_; 
v_snd_368_ = lean_ctor_get(v_b_367_, 1);
v_snd_369_ = lean_ctor_get(v_a_366_, 1);
v___x_370_ = lean_nat_dec_lt(v_snd_368_, v_snd_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(lean_object* v_a_371_, lean_object* v_b_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_371_, v_b_372_);
lean_dec_ref(v_b_372_);
lean_dec_ref(v_a_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(lean_object* v_n_375_, lean_object* v_as_376_, lean_object* v_lo_377_, lean_object* v_hi_378_){
_start:
{
lean_object* v___y_380_; uint8_t v___x_390_; 
v___x_390_ = lean_nat_dec_lt(v_lo_377_, v_hi_378_);
if (v___x_390_ == 0)
{
lean_dec(v_lo_377_);
return v_as_376_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_mid_393_; lean_object* v___y_395_; lean_object* v___y_401_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_391_ = lean_nat_add(v_lo_377_, v_hi_378_);
v___x_392_ = lean_unsigned_to_nat(1u);
v_mid_393_ = lean_nat_shiftr(v___x_391_, v___x_392_);
lean_dec(v___x_391_);
v___x_406_ = lean_array_fget_borrowed(v_as_376_, v_mid_393_);
v___x_407_ = lean_array_fget_borrowed(v_as_376_, v_lo_377_);
v___x_408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
v___y_401_ = v_as_376_;
goto v___jp_400_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_array_fswap(v_as_376_, v_lo_377_, v_mid_393_);
v___y_401_ = v___x_409_;
goto v___jp_400_;
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_396_ = lean_array_fget_borrowed(v___y_395_, v_mid_393_);
v___x_397_ = lean_array_fget_borrowed(v___y_395_, v_hi_378_);
v___x_398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec(v_mid_393_);
v___y_380_ = v___y_395_;
goto v___jp_379_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_array_fswap(v___y_395_, v_mid_393_, v_hi_378_);
lean_dec(v_mid_393_);
v___y_380_ = v___x_399_;
goto v___jp_379_;
}
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_array_fget_borrowed(v___y_401_, v_hi_378_);
v___x_403_ = lean_array_fget_borrowed(v___y_401_, v_lo_377_);
v___x_404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
v___y_395_ = v___y_401_;
goto v___jp_394_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_array_fswap(v___y_401_, v_lo_377_, v_hi_378_);
v___y_395_ = v___x_405_;
goto v___jp_394_;
}
}
}
v___jp_379_:
{
lean_object* v_pivot_381_; lean_object* v___x_382_; lean_object* v_fst_383_; lean_object* v_snd_384_; uint8_t v___x_385_; 
v_pivot_381_ = lean_array_fget(v___y_380_, v_hi_378_);
lean_inc_n(v_lo_377_, 2);
v___x_382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_378_, v_pivot_381_, v___y_380_, v_lo_377_, v_lo_377_);
lean_dec(v_pivot_381_);
v_fst_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_fst_383_);
v_snd_384_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_snd_384_);
lean_dec_ref(v___x_382_);
v___x_385_ = lean_nat_dec_le(v_hi_378_, v_fst_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_375_, v_snd_384_, v_lo_377_, v_fst_383_);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_fst_383_, v___x_387_);
lean_dec(v_fst_383_);
v_as_376_ = v___x_386_;
v_lo_377_ = v___x_388_;
goto _start;
}
else
{
lean_dec(v_fst_383_);
lean_dec(v_lo_377_);
return v_snd_384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(lean_object* v_n_410_, lean_object* v_as_411_, lean_object* v_lo_412_, lean_object* v_hi_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_410_, v_as_411_, v_lo_412_, v_hi_413_);
lean_dec(v_hi_413_);
lean_dec(v_n_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps(lean_object* v_e_417_, lean_object* v_threshold_418_){
_start:
{
lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v_counters_433_; lean_object* v___x_434_; lean_object* v_result_435_; lean_object* v___x_436_; lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_453_; 
v_counters_433_ = l_Lean_Expr_NumApps_main(v_e_417_);
v___x_434_ = lean_unsigned_to_nat(0u);
v_result_435_ = ((lean_object*)(l_Lean_Expr_numApps___closed__0));
v___x_436_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_418_, v_result_435_, v_counters_433_);
lean_dec(v_counters_433_);
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_453_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_453_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_453_;
goto v_resetjp_438_;
}
v___jp_420_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v___y_421_, v___y_423_, v___y_422_, v___y_424_);
lean_dec(v___y_424_);
lean_dec(v___y_421_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
v___jp_427_:
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_le(v___y_431_, v___y_429_);
if (v___x_432_ == 0)
{
lean_dec(v___y_429_);
lean_inc(v___y_431_);
v___y_421_ = v___y_428_;
v___y_422_ = v___y_431_;
v___y_423_ = v___y_430_;
v___y_424_ = v___y_431_;
goto v___jp_420_;
}
else
{
v___y_421_ = v___y_428_;
v___y_422_ = v___y_431_;
v___y_423_ = v___y_430_;
v___y_424_ = v___y_429_;
goto v___jp_420_;
}
}
v_resetjp_438_:
{
lean_object* v___y_442_; lean_object* v_a_443_; lean_object* v_a_449_; lean_object* v___x_451_; 
v_a_449_ = lean_ctor_get(v_a_437_, 0);
lean_inc_n(v_a_449_, 2);
lean_dec(v_a_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_a_449_);
v___x_451_ = v___x_439_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v___jp_441_:
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_array_get_size(v_a_443_);
v___x_445_ = lean_nat_dec_eq(v___x_444_, v___x_434_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
lean_dec_ref(v___y_442_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_sub(v___x_444_, v___x_446_);
v___x_448_ = lean_nat_dec_le(v___x_434_, v___x_447_);
if (v___x_448_ == 0)
{
lean_inc(v___x_447_);
v___y_428_ = v___x_444_;
v___y_429_ = v___x_447_;
v___y_430_ = v_a_443_;
v___y_431_ = v___x_447_;
goto v___jp_427_;
}
else
{
v___y_428_ = v___x_444_;
v___y_429_ = v___x_447_;
v___y_430_ = v_a_443_;
v___y_431_ = v___x_434_;
goto v___jp_427_;
}
}
else
{
lean_dec_ref(v_a_443_);
return v___y_442_;
}
}
v_reusejp_450_:
{
v___y_442_ = v___x_451_;
v_a_443_ = v_a_449_;
goto v___jp_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps___boxed(lean_object* v_e_454_, lean_object* v_threshold_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Expr_numApps(v_e_454_, v_threshold_455_);
lean_dec(v_threshold_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(lean_object* v_n_458_, lean_object* v_as_459_, lean_object* v_lo_460_, lean_object* v_hi_461_, lean_object* v_w_462_, lean_object* v_hlo_463_, lean_object* v_hhi_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_458_, v_as_459_, v_lo_460_, v_hi_461_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(lean_object* v_n_466_, lean_object* v_as_467_, lean_object* v_lo_468_, lean_object* v_hi_469_, lean_object* v_w_470_, lean_object* v_hlo_471_, lean_object* v_hhi_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(v_n_466_, v_as_467_, v_lo_468_, v_hi_469_, v_w_470_, v_hlo_471_, v_hhi_472_);
lean_dec(v_hi_469_);
lean_dec(v_n_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(lean_object* v_n_474_, lean_object* v_lo_475_, lean_object* v_hi_476_, lean_object* v_hhi_477_, lean_object* v_pivot_478_, lean_object* v_as_479_, lean_object* v_i_480_, lean_object* v_k_481_, lean_object* v_ilo_482_, lean_object* v_ik_483_, lean_object* v_w_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_476_, v_pivot_478_, v_as_479_, v_i_480_, v_k_481_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(lean_object* v_n_486_, lean_object* v_lo_487_, lean_object* v_hi_488_, lean_object* v_hhi_489_, lean_object* v_pivot_490_, lean_object* v_as_491_, lean_object* v_i_492_, lean_object* v_k_493_, lean_object* v_ilo_494_, lean_object* v_ik_495_, lean_object* v_w_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(v_n_486_, v_lo_487_, v_hi_488_, v_hhi_489_, v_pivot_490_, v_as_491_, v_i_492_, v_k_493_, v_ilo_494_, v_ik_495_, v_w_496_);
lean_dec_ref(v_pivot_490_);
lean_dec(v_hi_488_);
lean_dec(v_lo_487_);
lean_dec(v_n_486_);
return v_res_497_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_NumApps(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_NumApps(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_NumApps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_NumApps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_NumApps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_NumApps(builtin);
}
#ifdef __cplusplus
}
#endif
