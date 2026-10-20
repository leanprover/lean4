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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_nbuckets_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_45_ = lean_array_get_size(v_data_44_);
v___x_46_ = lean_unsigned_to_nat(2u);
v_nbuckets_47_ = lean_nat_mul(v___x_45_, v___x_46_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_box(0);
v___x_50_ = lean_mk_array(v_nbuckets_47_, v___x_49_);
v___x_51_ = lean_array_propagate_mark(v_data_44_, v___x_50_);
v___x_52_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v___x_48_, v_data_44_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(lean_object* v_a_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
else
{
lean_object* v_key_56_; lean_object* v_tail_57_; size_t v___x_58_; size_t v___x_59_; uint8_t v___x_60_; 
v_key_56_ = lean_ctor_get(v_x_54_, 0);
v_tail_57_ = lean_ctor_get(v_x_54_, 2);
v___x_58_ = lean_ptr_addr(v_key_56_);
v___x_59_ = lean_ptr_addr(v_a_53_);
v___x_60_ = lean_usize_dec_eq(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
v_x_54_ = v_tail_57_;
goto _start;
}
else
{
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_62_, lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_62_, v_x_63_);
lean_dec(v_x_63_);
lean_dec_ref(v_a_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(lean_object* v_m_66_, lean_object* v_a_67_, lean_object* v_b_68_){
_start:
{
lean_object* v_size_69_; lean_object* v_buckets_70_; lean_object* v___x_71_; size_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v_fold_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v_bkt_87_; uint8_t v___x_88_; 
v_size_69_ = lean_ctor_get(v_m_66_, 0);
v_buckets_70_ = lean_ctor_get(v_m_66_, 1);
v___x_71_ = lean_array_get_size(v_buckets_70_);
v___x_72_ = lean_ptr_addr(v_a_67_);
v___x_73_ = lean_usize_to_uint64(v___x_72_);
v___x_74_ = 11ULL;
v___x_75_ = lean_uint64_mix_hash(v___x_73_, v___x_74_);
v___x_76_ = 32ULL;
v___x_77_ = lean_uint64_shift_right(v___x_75_, v___x_76_);
v_fold_78_ = lean_uint64_xor(v___x_75_, v___x_77_);
v___x_79_ = 16ULL;
v___x_80_ = lean_uint64_shift_right(v_fold_78_, v___x_79_);
v___x_81_ = lean_uint64_xor(v_fold_78_, v___x_80_);
v___x_82_ = lean_uint64_to_usize(v___x_81_);
v___x_83_ = lean_usize_of_nat(v___x_71_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_sub(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_land(v___x_82_, v___x_85_);
v_bkt_87_ = lean_array_uget_borrowed(v_buckets_70_, v___x_86_);
v___x_88_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_67_, v_bkt_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_109_; 
lean_inc_ref(v_buckets_70_);
lean_inc(v_size_69_);
v_isSharedCheck_109_ = !lean_is_exclusive(v_m_66_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; lean_object* v_unused_111_; 
v_unused_110_ = lean_ctor_get(v_m_66_, 1);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_m_66_, 0);
lean_dec(v_unused_111_);
v___x_90_ = v_m_66_;
v_isShared_91_ = v_isSharedCheck_109_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_m_66_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_109_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v_size_x27_93_; lean_object* v___x_94_; lean_object* v_buckets_x27_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v_size_x27_93_ = lean_nat_add(v_size_69_, v___x_92_);
lean_dec(v_size_69_);
lean_inc(v_bkt_87_);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v_a_67_);
lean_ctor_set(v___x_94_, 1, v_b_68_);
lean_ctor_set(v___x_94_, 2, v_bkt_87_);
v_buckets_x27_95_ = lean_array_uset(v_buckets_70_, v___x_86_, v___x_94_);
v___x_96_ = lean_unsigned_to_nat(4u);
v___x_97_ = lean_nat_mul(v_size_x27_93_, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = lean_nat_div(v___x_97_, v___x_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_array_get_size(v_buckets_x27_95_);
v___x_101_ = lean_nat_dec_le(v___x_99_, v___x_100_);
lean_dec(v___x_99_);
if (v___x_101_ == 0)
{
lean_object* v_val_102_; lean_object* v___x_104_; 
v_val_102_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_buckets_x27_95_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_val_102_);
lean_ctor_set(v___x_90_, 0, v_size_x27_93_);
v___x_104_ = v___x_90_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_size_x27_93_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_val_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v___x_107_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_buckets_x27_95_);
lean_ctor_set(v___x_90_, 0, v_size_x27_93_);
v___x_107_ = v___x_90_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_size_x27_93_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_buckets_x27_95_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_dec(v_b_68_);
lean_dec_ref(v_a_67_);
return v_m_66_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(lean_object* v_m_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_buckets_114_; lean_object* v___x_115_; size_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_buckets_114_ = lean_ctor_get(v_m_112_, 1);
v___x_115_ = lean_array_get_size(v_buckets_114_);
v___x_116_ = lean_ptr_addr(v_a_113_);
v___x_117_ = lean_usize_to_uint64(v___x_116_);
v___x_118_ = 11ULL;
v___x_119_ = lean_uint64_mix_hash(v___x_117_, v___x_118_);
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___x_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___x_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_115_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_array_uget_borrowed(v_buckets_114_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_113_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(lean_object* v_m_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_133_, v_a_134_);
lean_dec_ref(v_a_134_);
lean_dec_ref(v_m_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_visit___closed__0(void){
_start:
{
lean_object* v___x_137_; lean_object* v_dummy_138_; 
v___x_137_ = lean_box(0);
v_dummy_138_ = l_Lean_Expr_sort___override(v___x_137_);
return v_dummy_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___y_144_; 
if (lean_obj_tag(v_x_139_) == 5)
{
lean_object* v_fn_162_; lean_object* v_arg_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_fn_162_ = lean_ctor_get(v_x_139_, 0);
lean_inc_ref(v_fn_162_);
v_arg_163_ = lean_ctor_get(v_x_139_, 1);
lean_inc_ref(v_arg_163_);
lean_dec_ref_known(v_x_139_, 2);
v___x_164_ = lean_array_set(v_x_140_, v_x_141_, v_arg_163_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_sub(v_x_141_, v___x_165_);
lean_dec(v_x_141_);
v_x_139_ = v_fn_162_;
v_x_140_ = v___x_164_;
v_x_141_ = v___x_166_;
goto _start;
}
else
{
lean_dec(v_x_141_);
if (lean_obj_tag(v_x_139_) == 4)
{
lean_object* v_declName_168_; lean_object* v_visited_169_; lean_object* v_counters_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_185_; 
v_declName_168_ = lean_ctor_get(v_x_139_, 0);
v_visited_169_ = lean_ctor_get(v___y_142_, 0);
v_counters_170_ = lean_ctor_get(v___y_142_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___y_142_);
if (v_isSharedCheck_185_ == 0)
{
v___x_172_ = v___y_142_;
v_isShared_173_ = v_isSharedCheck_185_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_counters_170_);
lean_inc(v_visited_169_);
lean_dec(v___y_142_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_185_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___y_175_; lean_object* v___x_182_; 
v___x_182_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_counters_170_, v_declName_168_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___y_175_ = v___x_183_;
goto v___jp_174_;
}
else
{
lean_object* v_val_184_; 
v_val_184_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v___x_182_, 1);
v___y_175_ = v_val_184_;
goto v___jp_174_;
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_add(v___y_175_, v___x_176_);
lean_dec(v___y_175_);
lean_inc(v_declName_168_);
v___x_178_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_168_, v___x_177_, v_counters_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_178_);
v___x_180_ = v___x_172_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_visited_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v___y_144_ = v___x_180_;
goto v___jp_143_;
}
}
}
}
else
{
v___y_144_ = v___y_142_;
goto v___jp_143_;
}
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v_snd_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_160_; 
v___x_145_ = l_Lean_Expr_NumApps_visit(v_x_139_, v___y_144_);
v_snd_146_ = lean_ctor_get(v___x_145_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_145_, 0);
lean_dec(v_unused_161_);
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_160_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snd_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_160_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_array_get_size(v_x_140_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v_x_140_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_152_);
v___x_155_ = v___x_148_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_snd_146_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
lean_del_object(v___x_148_);
v___x_157_ = ((size_t)0ULL);
v___x_158_ = lean_usize_of_nat(v___x_151_);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_140_, v___x_157_, v___x_158_, v___x_152_, v_snd_146_);
lean_dec_ref(v_x_140_);
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object* v_e_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_d_189_; lean_object* v_b_190_; lean_object* v___y_191_; lean_object* v_visited_195_; lean_object* v_counters_196_; uint8_t v___x_197_; 
v_visited_195_ = lean_ctor_get(v_a_187_, 0);
v_counters_196_ = lean_ctor_get(v_a_187_, 1);
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_visited_195_, v_e_186_);
if (v___x_197_ == 0)
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_229_; 
lean_inc(v_counters_196_);
lean_inc_ref(v_visited_195_);
v_isSharedCheck_229_ = !lean_is_exclusive(v_a_187_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_230_ = lean_ctor_get(v_a_187_, 1);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_a_187_, 0);
lean_dec(v_unused_231_);
v___x_199_ = v_a_187_;
v_isShared_200_ = v_isSharedCheck_229_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_a_187_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_229_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_box(0);
lean_inc_ref(v_e_186_);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_visited_195_, v_e_186_, v___x_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_204_ = v___x_199_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_counters_196_);
v___x_204_ = v_reuseFailAlloc_228_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
switch(lean_obj_tag(v_e_186_))
{
case 7:
{
lean_object* v_binderType_205_; lean_object* v_body_206_; 
v_binderType_205_ = lean_ctor_get(v_e_186_, 1);
lean_inc_ref(v_binderType_205_);
v_body_206_ = lean_ctor_get(v_e_186_, 2);
lean_inc_ref(v_body_206_);
lean_dec_ref_known(v_e_186_, 3);
v_d_189_ = v_binderType_205_;
v_b_190_ = v_body_206_;
v___y_191_ = v___x_204_;
goto v___jp_188_;
}
case 6:
{
lean_object* v_binderType_207_; lean_object* v_body_208_; 
v_binderType_207_ = lean_ctor_get(v_e_186_, 1);
lean_inc_ref(v_binderType_207_);
v_body_208_ = lean_ctor_get(v_e_186_, 2);
lean_inc_ref(v_body_208_);
lean_dec_ref_known(v_e_186_, 3);
v_d_189_ = v_binderType_207_;
v_b_190_ = v_body_208_;
v___y_191_ = v___x_204_;
goto v___jp_188_;
}
case 10:
{
lean_object* v_expr_209_; 
v_expr_209_ = lean_ctor_get(v_e_186_, 1);
lean_inc_ref(v_expr_209_);
lean_dec_ref_known(v_e_186_, 2);
v_e_186_ = v_expr_209_;
v_a_187_ = v___x_204_;
goto _start;
}
case 8:
{
lean_object* v_type_211_; lean_object* v_value_212_; lean_object* v_body_213_; lean_object* v___x_214_; lean_object* v_snd_215_; lean_object* v___x_216_; lean_object* v_snd_217_; 
v_type_211_ = lean_ctor_get(v_e_186_, 1);
lean_inc_ref(v_type_211_);
v_value_212_ = lean_ctor_get(v_e_186_, 2);
lean_inc_ref(v_value_212_);
v_body_213_ = lean_ctor_get(v_e_186_, 3);
lean_inc_ref(v_body_213_);
lean_dec_ref_known(v_e_186_, 4);
v___x_214_ = l_Lean_Expr_NumApps_visit(v_type_211_, v___x_204_);
v_snd_215_ = lean_ctor_get(v___x_214_, 1);
lean_inc(v_snd_215_);
lean_dec_ref(v___x_214_);
v___x_216_ = l_Lean_Expr_NumApps_visit(v_value_212_, v_snd_215_);
v_snd_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_snd_217_);
lean_dec_ref(v___x_216_);
v_e_186_ = v_body_213_;
v_a_187_ = v_snd_217_;
goto _start;
}
case 5:
{
lean_object* v_dummy_219_; lean_object* v_nargs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_dummy_219_ = lean_obj_once(&l_Lean_Expr_NumApps_visit___closed__0, &l_Lean_Expr_NumApps_visit___closed__0_once, _init_l_Lean_Expr_NumApps_visit___closed__0);
v_nargs_220_ = l_Lean_Expr_getAppNumArgs(v_e_186_);
lean_inc(v_nargs_220_);
v___x_221_ = lean_mk_array(v_nargs_220_, v_dummy_219_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v_nargs_220_, v___x_222_);
lean_dec(v_nargs_220_);
v___x_224_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(v_e_186_, v___x_221_, v___x_223_, v___x_204_);
return v___x_224_;
}
case 11:
{
lean_object* v_struct_225_; 
v_struct_225_ = lean_ctor_get(v_e_186_, 2);
lean_inc_ref(v_struct_225_);
lean_dec_ref_known(v_e_186_, 3);
v_e_186_ = v_struct_225_;
v_a_187_ = v___x_204_;
goto _start;
}
default: 
{
lean_object* v___x_227_; 
lean_dec_ref(v_e_186_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_201_);
lean_ctor_set(v___x_227_, 1, v___x_204_);
return v___x_227_;
}
}
}
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v_e_186_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_a_187_);
return v___x_233_;
}
v___jp_188_:
{
lean_object* v___x_192_; lean_object* v_snd_193_; 
v___x_192_ = l_Lean_Expr_NumApps_visit(v_d_189_, v___y_191_);
v_snd_193_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_snd_193_);
lean_dec_ref(v___x_192_);
v_e_186_ = v_b_190_;
v_a_187_ = v_snd_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object* v_as_234_, size_t v_i_235_, size_t v_stop_236_, lean_object* v_b_237_, lean_object* v___y_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_eq(v_i_235_, v_stop_236_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; size_t v___x_244_; size_t v___x_245_; 
v___x_240_ = lean_array_uget_borrowed(v_as_234_, v_i_235_);
lean_inc(v___x_240_);
v___x_241_ = l_Lean_Expr_NumApps_visit(v___x_240_, v___y_238_);
v_fst_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_fst_242_);
v_snd_243_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v___x_241_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_235_, v___x_244_);
v_i_235_ = v___x_245_;
v_b_237_ = v_fst_242_;
v___y_238_ = v_snd_243_;
goto _start;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_b_237_);
lean_ctor_set(v___x_247_, 1, v___y_238_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object* v_as_248_, lean_object* v_i_249_, lean_object* v_stop_250_, lean_object* v_b_251_, lean_object* v___y_252_){
_start:
{
size_t v_i_boxed_253_; size_t v_stop_boxed_254_; lean_object* v_res_255_; 
v_i_boxed_253_ = lean_unbox_usize(v_i_249_);
lean_dec(v_i_249_);
v_stop_boxed_254_ = lean_unbox_usize(v_stop_250_);
lean_dec(v_stop_250_);
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_248_, v_i_boxed_253_, v_stop_boxed_254_, v_b_251_, v___y_252_);
lean_dec_ref(v_as_248_);
return v_res_255_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object* v_00_u03b2_256_, lean_object* v_m_257_, lean_object* v_a_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_257_, v_a_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object* v_00_u03b2_260_, lean_object* v_m_261_, lean_object* v_a_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(v_00_u03b2_260_, v_m_261_, v_a_262_);
lean_dec_ref(v_a_262_);
lean_dec_ref(v_m_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2(lean_object* v_00_u03b2_265_, lean_object* v_m_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_m_266_, v_a_267_, v_b_268_);
return v___x_269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object* v_00_u03b2_270_, lean_object* v_a_271_, lean_object* v_x_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_271_, v_x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_274_, lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(v_00_u03b2_274_, v_a_275_, v_x_276_);
lean_dec(v_x_276_);
lean_dec_ref(v_a_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3(lean_object* v_00_u03b2_279_, lean_object* v_data_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_data_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_282_, lean_object* v_i_283_, lean_object* v_source_284_, lean_object* v_target_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v_i_283_, v_source_284_, v_target_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_288_, v_x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__0(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(64u);
v___x_292_ = l_Lean_mkPtrSet___redArg(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_box(1);
v___x_294_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__0, &l_Lean_Expr_NumApps_main___closed__0_once, _init_l_Lean_Expr_NumApps_main___closed__0);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_main(lean_object* v_e_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_snd_299_; lean_object* v_counters_300_; 
v___x_297_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__1, &l_Lean_Expr_NumApps_main___closed__1_once, _init_l_Lean_Expr_NumApps_main___closed__1);
v___x_298_ = l_Lean_Expr_NumApps_visit(v_e_296_, v___x_297_);
v_snd_299_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_snd_299_);
lean_dec_ref(v___x_298_);
v_counters_300_ = lean_ctor_get(v_snd_299_, 1);
lean_inc(v_counters_300_);
lean_dec(v_snd_299_);
return v_counters_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(lean_object* v_e_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Expr_NumApps_main(v_e_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(lean_object* v_threshold_303_, lean_object* v_init_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v_k_307_; lean_object* v_v_308_; lean_object* v_l_309_; lean_object* v_r_310_; lean_object* v___x_311_; lean_object* v_a_312_; lean_object* v_a_313_; uint8_t v___x_314_; 
v_k_307_ = lean_ctor_get(v_x_305_, 1);
v_v_308_ = lean_ctor_get(v_x_305_, 2);
v_l_309_ = lean_ctor_get(v_x_305_, 3);
v_r_310_ = lean_ctor_get(v_x_305_, 4);
v___x_311_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_303_, v_init_304_, v_l_309_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___x_311_);
v_a_313_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_a_313_);
lean_dec(v_a_312_);
v___x_314_ = lean_nat_dec_lt(v_threshold_303_, v_v_308_);
if (v___x_314_ == 0)
{
v_init_304_ = v_a_313_;
v_x_305_ = v_r_310_;
goto _start;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc(v_v_308_);
lean_inc(v_k_307_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_k_307_);
lean_ctor_set(v___x_316_, 1, v_v_308_);
v___x_317_ = lean_array_push(v_a_313_, v___x_316_);
v_init_304_ = v___x_317_;
v_x_305_ = v_r_310_;
goto _start;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v_init_304_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(lean_object* v_threshold_321_, lean_object* v_init_322_, lean_object* v_x_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_321_, v_init_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec(v_threshold_321_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(lean_object* v_hi_326_, lean_object* v_pivot_327_, lean_object* v_as_328_, lean_object* v_i_329_, lean_object* v_k_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_lt(v_k_330_, v_hi_326_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_k_330_);
v___x_332_ = lean_array_fswap(v_as_328_, v_i_329_, v_hi_326_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_i_329_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
return v___x_333_;
}
else
{
lean_object* v_snd_334_; lean_object* v___x_335_; lean_object* v_snd_336_; uint8_t v___x_337_; 
v_snd_334_ = lean_ctor_get(v_pivot_327_, 1);
v___x_335_ = lean_array_fget_borrowed(v_as_328_, v_k_330_);
v_snd_336_ = lean_ctor_get(v___x_335_, 1);
v___x_337_ = lean_nat_dec_lt(v_snd_334_, v_snd_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_k_330_, v___x_338_);
lean_dec(v_k_330_);
v_k_330_ = v___x_339_;
goto _start;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_341_ = lean_array_fswap(v_as_328_, v_i_329_, v_k_330_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_329_, v___x_342_);
lean_dec(v_i_329_);
v___x_344_ = lean_nat_add(v_k_330_, v___x_342_);
lean_dec(v_k_330_);
v_as_328_ = v___x_341_;
v_i_329_ = v___x_343_;
v_k_330_ = v___x_344_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_346_, lean_object* v_pivot_347_, lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_k_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_346_, v_pivot_347_, v_as_348_, v_i_349_, v_k_350_);
lean_dec_ref(v_pivot_347_);
lean_dec(v_hi_346_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(lean_object* v_a_352_, lean_object* v_b_353_){
_start:
{
lean_object* v_snd_354_; lean_object* v_snd_355_; uint8_t v___x_356_; 
v_snd_354_ = lean_ctor_get(v_b_353_, 1);
v_snd_355_ = lean_ctor_get(v_a_352_, 1);
v___x_356_ = lean_nat_dec_lt(v_snd_354_, v_snd_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_357_, v_b_358_);
lean_dec_ref(v_b_358_);
lean_dec_ref(v_a_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(lean_object* v_n_361_, lean_object* v_as_362_, lean_object* v_lo_363_, lean_object* v_hi_364_){
_start:
{
lean_object* v___y_366_; uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_lt(v_lo_363_, v_hi_364_);
if (v___x_376_ == 0)
{
lean_dec(v_lo_363_);
return v_as_362_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_mid_379_; lean_object* v___y_381_; lean_object* v___y_387_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_377_ = lean_nat_add(v_lo_363_, v_hi_364_);
v___x_378_ = lean_unsigned_to_nat(1u);
v_mid_379_ = lean_nat_shiftr(v___x_377_, v___x_378_);
lean_dec(v___x_377_);
v___x_392_ = lean_array_fget_borrowed(v_as_362_, v_mid_379_);
v___x_393_ = lean_array_fget_borrowed(v_as_362_, v_lo_363_);
v___x_394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
v___y_387_ = v_as_362_;
goto v___jp_386_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = lean_array_fswap(v_as_362_, v_lo_363_, v_mid_379_);
v___y_387_ = v___x_395_;
goto v___jp_386_;
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_array_fget_borrowed(v___y_381_, v_mid_379_);
v___x_383_ = lean_array_fget_borrowed(v___y_381_, v_hi_364_);
v___x_384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v_mid_379_);
v___y_366_ = v___y_381_;
goto v___jp_365_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_array_fswap(v___y_381_, v_mid_379_, v_hi_364_);
lean_dec(v_mid_379_);
v___y_366_ = v___x_385_;
goto v___jp_365_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = lean_array_fget_borrowed(v___y_387_, v_hi_364_);
v___x_389_ = lean_array_fget_borrowed(v___y_387_, v_lo_363_);
v___x_390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
v___y_381_ = v___y_387_;
goto v___jp_380_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_array_fswap(v___y_387_, v_lo_363_, v_hi_364_);
v___y_381_ = v___x_391_;
goto v___jp_380_;
}
}
}
v___jp_365_:
{
lean_object* v_pivot_367_; lean_object* v___x_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; uint8_t v___x_371_; 
v_pivot_367_ = lean_array_fget(v___y_366_, v_hi_364_);
lean_inc_n(v_lo_363_, 2);
v___x_368_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_364_, v_pivot_367_, v___y_366_, v_lo_363_, v_lo_363_);
lean_dec(v_pivot_367_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_snd_370_);
lean_dec_ref(v___x_368_);
v___x_371_ = lean_nat_dec_le(v_hi_364_, v_fst_369_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_361_, v_snd_370_, v_lo_363_, v_fst_369_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_fst_369_, v___x_373_);
lean_dec(v_fst_369_);
v_as_362_ = v___x_372_;
v_lo_363_ = v___x_374_;
goto _start;
}
else
{
lean_dec(v_fst_369_);
lean_dec(v_lo_363_);
return v_snd_370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(lean_object* v_n_396_, lean_object* v_as_397_, lean_object* v_lo_398_, lean_object* v_hi_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_396_, v_as_397_, v_lo_398_, v_hi_399_);
lean_dec(v_hi_399_);
lean_dec(v_n_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps(lean_object* v_e_403_, lean_object* v_threshold_404_){
_start:
{
lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_420_; lean_object* v_a_421_; lean_object* v_counters_428_; lean_object* v_result_429_; lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_counters_428_ = l_Lean_Expr_NumApps_main(v_e_403_);
v_result_429_ = ((lean_object*)(l_Lean_Expr_numApps___closed__0));
v___x_430_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_404_, v_result_429_, v_counters_428_);
lean_dec(v_counters_428_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v___jp_406_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v___y_408_, v___y_409_, v___y_407_, v___y_410_);
lean_dec(v___y_410_);
lean_dec(v___y_408_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
v___jp_413_:
{
uint8_t v___x_418_; 
v___x_418_ = lean_nat_dec_le(v___y_417_, v___y_414_);
if (v___x_418_ == 0)
{
lean_dec(v___y_414_);
lean_inc(v___y_417_);
v___y_407_ = v___y_417_;
v___y_408_ = v___y_415_;
v___y_409_ = v___y_416_;
v___y_410_ = v___y_417_;
goto v___jp_406_;
}
else
{
v___y_407_ = v___y_417_;
v___y_408_ = v___y_415_;
v___y_409_ = v___y_416_;
v___y_410_ = v___y_414_;
goto v___jp_406_;
}
}
v___jp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_array_get_size(v_a_421_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_nat_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
lean_dec_ref(v___y_420_);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_nat_sub(v___x_422_, v___x_425_);
v___x_427_ = lean_nat_dec_le(v___x_423_, v___x_426_);
if (v___x_427_ == 0)
{
lean_inc(v___x_426_);
v___y_414_ = v___x_426_;
v___y_415_ = v___x_422_;
v___y_416_ = v_a_421_;
v___y_417_ = v___x_426_;
goto v___jp_413_;
}
else
{
v___y_414_ = v___x_426_;
v___y_415_ = v___x_422_;
v___y_416_ = v_a_421_;
v___y_417_ = v___x_423_;
goto v___jp_413_;
}
}
else
{
lean_dec_ref(v_a_421_);
return v___y_420_;
}
}
v_resetjp_432_:
{
lean_object* v_a_435_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v_a_431_, 0);
lean_inc_n(v_a_435_, 2);
lean_dec(v_a_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_a_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v___y_420_ = v___x_437_;
v_a_421_ = v_a_435_;
goto v___jp_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps___boxed(lean_object* v_e_440_, lean_object* v_threshold_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Expr_numApps(v_e_440_, v_threshold_441_);
lean_dec(v_threshold_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(lean_object* v_n_444_, lean_object* v_as_445_, lean_object* v_lo_446_, lean_object* v_hi_447_, lean_object* v_w_448_, lean_object* v_hlo_449_, lean_object* v_hhi_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_444_, v_as_445_, v_lo_446_, v_hi_447_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(lean_object* v_n_452_, lean_object* v_as_453_, lean_object* v_lo_454_, lean_object* v_hi_455_, lean_object* v_w_456_, lean_object* v_hlo_457_, lean_object* v_hhi_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(v_n_452_, v_as_453_, v_lo_454_, v_hi_455_, v_w_456_, v_hlo_457_, v_hhi_458_);
lean_dec(v_hi_455_);
lean_dec(v_n_452_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(lean_object* v_n_460_, lean_object* v_lo_461_, lean_object* v_hi_462_, lean_object* v_hhi_463_, lean_object* v_pivot_464_, lean_object* v_as_465_, lean_object* v_i_466_, lean_object* v_k_467_, lean_object* v_ilo_468_, lean_object* v_ik_469_, lean_object* v_w_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_462_, v_pivot_464_, v_as_465_, v_i_466_, v_k_467_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(lean_object* v_n_472_, lean_object* v_lo_473_, lean_object* v_hi_474_, lean_object* v_hhi_475_, lean_object* v_pivot_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_k_479_, lean_object* v_ilo_480_, lean_object* v_ik_481_, lean_object* v_w_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(v_n_472_, v_lo_473_, v_hi_474_, v_hhi_475_, v_pivot_476_, v_as_477_, v_i_478_, v_k_479_, v_ilo_480_, v_ik_481_, v_w_482_);
lean_dec_ref(v_pivot_476_);
lean_dec(v_hi_474_);
lean_dec(v_lo_473_);
lean_dec(v_n_472_);
return v_res_483_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_NumApps(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
