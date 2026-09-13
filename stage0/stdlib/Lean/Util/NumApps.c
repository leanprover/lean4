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
lean_object* v_fn_169_; lean_object* v_arg_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_fn_169_ = lean_ctor_get(v_x_139_, 0);
lean_inc_ref(v_fn_169_);
v_arg_170_ = lean_ctor_get(v_x_139_, 1);
lean_inc_ref(v_arg_170_);
lean_dec_ref_known(v_x_139_, 2);
v___x_171_ = lean_array_set(v_x_140_, v_x_141_, v_arg_170_);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_sub(v_x_141_, v___x_172_);
lean_dec(v_x_141_);
v_x_139_ = v_fn_169_;
v_x_140_ = v___x_171_;
v_x_141_ = v___x_173_;
goto _start;
}
else
{
lean_dec(v_x_141_);
if (lean_obj_tag(v_x_139_) == 4)
{
lean_object* v_declName_175_; lean_object* v_visited_176_; lean_object* v_counters_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_192_; 
v_declName_175_ = lean_ctor_get(v_x_139_, 0);
v_visited_176_ = lean_ctor_get(v___y_142_, 0);
v_counters_177_ = lean_ctor_get(v___y_142_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___y_142_);
if (v_isSharedCheck_192_ == 0)
{
v___x_179_ = v___y_142_;
v_isShared_180_ = v_isSharedCheck_192_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_counters_177_);
lean_inc(v_visited_176_);
lean_dec(v___y_142_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_192_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___y_182_; lean_object* v___x_189_; 
v___x_189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_counters_177_, v_declName_175_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___y_182_ = v___x_190_;
goto v___jp_181_;
}
else
{
lean_object* v_val_191_; 
v_val_191_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v___x_189_, 1);
v___y_182_ = v_val_191_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v___y_182_, v___x_183_);
lean_dec(v___y_182_);
lean_inc(v_declName_175_);
v___x_185_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_175_, v___x_184_, v_counters_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_185_);
v___x_187_ = v___x_179_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_visited_176_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v___y_144_ = v___x_187_;
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
lean_object* v___x_145_; lean_object* v_snd_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_167_; 
v___x_145_ = l_Lean_Expr_NumApps_visit(v_x_139_, v___y_144_);
v_snd_146_ = lean_ctor_get(v___x_145_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v___x_145_, 0);
lean_dec(v_unused_168_);
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_167_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snd_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_167_;
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
uint8_t v___x_157_; 
v___x_157_ = lean_nat_dec_le(v___x_151_, v___x_151_);
if (v___x_157_ == 0)
{
if (v___x_153_ == 0)
{
lean_object* v___x_159_; 
lean_dec_ref(v_x_140_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_152_);
v___x_159_ = v___x_148_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_snd_146_);
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
size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
lean_del_object(v___x_148_);
v___x_161_ = ((size_t)0ULL);
v___x_162_ = lean_usize_of_nat(v___x_151_);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_140_, v___x_161_, v___x_162_, v___x_152_, v_snd_146_);
lean_dec_ref(v_x_140_);
return v___x_163_;
}
}
else
{
size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
lean_del_object(v___x_148_);
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_151_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_140_, v___x_164_, v___x_165_, v___x_152_, v_snd_146_);
lean_dec_ref(v_x_140_);
return v___x_166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object* v_e_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_d_196_; lean_object* v_b_197_; lean_object* v___y_198_; lean_object* v_visited_202_; lean_object* v_counters_203_; uint8_t v___x_204_; 
v_visited_202_ = lean_ctor_get(v_a_194_, 0);
v_counters_203_ = lean_ctor_get(v_a_194_, 1);
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_visited_202_, v_e_193_);
if (v___x_204_ == 0)
{
lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_236_; 
lean_inc(v_counters_203_);
lean_inc_ref(v_visited_202_);
v_isSharedCheck_236_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_237_ = lean_ctor_get(v_a_194_, 1);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_a_194_, 0);
lean_dec(v_unused_238_);
v___x_206_ = v_a_194_;
v_isShared_207_ = v_isSharedCheck_236_;
goto v_resetjp_205_;
}
else
{
lean_dec(v_a_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_236_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = lean_box(0);
lean_inc_ref(v_e_193_);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_visited_202_, v_e_193_, v___x_208_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_209_);
v___x_211_ = v___x_206_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_counters_203_);
v___x_211_ = v_reuseFailAlloc_235_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
switch(lean_obj_tag(v_e_193_))
{
case 7:
{
lean_object* v_binderType_212_; lean_object* v_body_213_; 
v_binderType_212_ = lean_ctor_get(v_e_193_, 1);
lean_inc_ref(v_binderType_212_);
v_body_213_ = lean_ctor_get(v_e_193_, 2);
lean_inc_ref(v_body_213_);
lean_dec_ref_known(v_e_193_, 3);
v_d_196_ = v_binderType_212_;
v_b_197_ = v_body_213_;
v___y_198_ = v___x_211_;
goto v___jp_195_;
}
case 6:
{
lean_object* v_binderType_214_; lean_object* v_body_215_; 
v_binderType_214_ = lean_ctor_get(v_e_193_, 1);
lean_inc_ref(v_binderType_214_);
v_body_215_ = lean_ctor_get(v_e_193_, 2);
lean_inc_ref(v_body_215_);
lean_dec_ref_known(v_e_193_, 3);
v_d_196_ = v_binderType_214_;
v_b_197_ = v_body_215_;
v___y_198_ = v___x_211_;
goto v___jp_195_;
}
case 10:
{
lean_object* v_expr_216_; 
v_expr_216_ = lean_ctor_get(v_e_193_, 1);
lean_inc_ref(v_expr_216_);
lean_dec_ref_known(v_e_193_, 2);
v_e_193_ = v_expr_216_;
v_a_194_ = v___x_211_;
goto _start;
}
case 8:
{
lean_object* v_type_218_; lean_object* v_value_219_; lean_object* v_body_220_; lean_object* v___x_221_; lean_object* v_snd_222_; lean_object* v___x_223_; lean_object* v_snd_224_; 
v_type_218_ = lean_ctor_get(v_e_193_, 1);
lean_inc_ref(v_type_218_);
v_value_219_ = lean_ctor_get(v_e_193_, 2);
lean_inc_ref(v_value_219_);
v_body_220_ = lean_ctor_get(v_e_193_, 3);
lean_inc_ref(v_body_220_);
lean_dec_ref_known(v_e_193_, 4);
v___x_221_ = l_Lean_Expr_NumApps_visit(v_type_218_, v___x_211_);
v_snd_222_ = lean_ctor_get(v___x_221_, 1);
lean_inc(v_snd_222_);
lean_dec_ref(v___x_221_);
v___x_223_ = l_Lean_Expr_NumApps_visit(v_value_219_, v_snd_222_);
v_snd_224_ = lean_ctor_get(v___x_223_, 1);
lean_inc(v_snd_224_);
lean_dec_ref(v___x_223_);
v_e_193_ = v_body_220_;
v_a_194_ = v_snd_224_;
goto _start;
}
case 5:
{
lean_object* v_dummy_226_; lean_object* v_nargs_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_dummy_226_ = lean_obj_once(&l_Lean_Expr_NumApps_visit___closed__0, &l_Lean_Expr_NumApps_visit___closed__0_once, _init_l_Lean_Expr_NumApps_visit___closed__0);
v_nargs_227_ = l_Lean_Expr_getAppNumArgs(v_e_193_);
lean_inc(v_nargs_227_);
v___x_228_ = lean_mk_array(v_nargs_227_, v_dummy_226_);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_sub(v_nargs_227_, v___x_229_);
lean_dec(v_nargs_227_);
v___x_231_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(v_e_193_, v___x_228_, v___x_230_, v___x_211_);
return v___x_231_;
}
case 11:
{
lean_object* v_struct_232_; 
v_struct_232_ = lean_ctor_get(v_e_193_, 2);
lean_inc_ref(v_struct_232_);
lean_dec_ref_known(v_e_193_, 3);
v_e_193_ = v_struct_232_;
v_a_194_ = v___x_211_;
goto _start;
}
default: 
{
lean_object* v___x_234_; 
lean_dec_ref(v_e_193_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_208_);
lean_ctor_set(v___x_234_, 1, v___x_211_);
return v___x_234_;
}
}
}
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v_e_193_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_a_194_);
return v___x_240_;
}
v___jp_195_:
{
lean_object* v___x_199_; lean_object* v_snd_200_; 
v___x_199_ = l_Lean_Expr_NumApps_visit(v_d_196_, v___y_198_);
v_snd_200_ = lean_ctor_get(v___x_199_, 1);
lean_inc(v_snd_200_);
lean_dec_ref(v___x_199_);
v_e_193_ = v_b_197_;
v_a_194_ = v_snd_200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object* v_as_241_, size_t v_i_242_, size_t v_stop_243_, lean_object* v_b_244_, lean_object* v___y_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_usize_dec_eq(v_i_242_, v_stop_243_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_fst_249_; lean_object* v_snd_250_; size_t v___x_251_; size_t v___x_252_; 
v___x_247_ = lean_array_uget_borrowed(v_as_241_, v_i_242_);
lean_inc(v___x_247_);
v___x_248_ = l_Lean_Expr_NumApps_visit(v___x_247_, v___y_245_);
v_fst_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_fst_249_);
v_snd_250_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_snd_250_);
lean_dec_ref(v___x_248_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_242_, v___x_251_);
v_i_242_ = v___x_252_;
v_b_244_ = v_fst_249_;
v___y_245_ = v_snd_250_;
goto _start;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_b_244_);
lean_ctor_set(v___x_254_, 1, v___y_245_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_, lean_object* v___y_259_){
_start:
{
size_t v_i_boxed_260_; size_t v_stop_boxed_261_; lean_object* v_res_262_; 
v_i_boxed_260_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_261_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_255_, v_i_boxed_260_, v_stop_boxed_261_, v_b_258_, v___y_259_);
lean_dec_ref(v_as_255_);
return v_res_262_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object* v_00_u03b2_263_, lean_object* v_m_264_, lean_object* v_a_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_264_, v_a_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object* v_00_u03b2_267_, lean_object* v_m_268_, lean_object* v_a_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(v_00_u03b2_267_, v_m_268_, v_a_269_);
lean_dec_ref(v_a_269_);
lean_dec_ref(v_m_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2(lean_object* v_00_u03b2_272_, lean_object* v_m_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_m_273_, v_a_274_, v_b_275_);
return v___x_276_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object* v_00_u03b2_277_, lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_278_, v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_281_, lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(v_00_u03b2_281_, v_a_282_, v_x_283_);
lean_dec(v_x_283_);
lean_dec_ref(v_a_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3(lean_object* v_00_u03b2_286_, lean_object* v_data_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_data_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_289_, lean_object* v_i_290_, lean_object* v_source_291_, lean_object* v_target_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v_i_290_, v_source_291_, v_target_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_295_, v_x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__0(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(64u);
v___x_299_ = l_Lean_mkPtrSet___redArg(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_box(1);
v___x_301_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__0, &l_Lean_Expr_NumApps_main___closed__0_once, _init_l_Lean_Expr_NumApps_main___closed__0);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_main(lean_object* v_e_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_snd_306_; lean_object* v_counters_307_; 
v___x_304_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__1, &l_Lean_Expr_NumApps_main___closed__1_once, _init_l_Lean_Expr_NumApps_main___closed__1);
v___x_305_ = l_Lean_Expr_NumApps_visit(v_e_303_, v___x_304_);
v_snd_306_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_306_);
lean_dec_ref(v___x_305_);
v_counters_307_ = lean_ctor_get(v_snd_306_, 1);
lean_inc(v_counters_307_);
lean_dec(v_snd_306_);
return v_counters_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(lean_object* v_e_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Expr_NumApps_main(v_e_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(lean_object* v_threshold_310_, lean_object* v_init_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_d_315_; 
if (lean_obj_tag(v_x_312_) == 0)
{
lean_object* v_k_318_; lean_object* v_v_319_; lean_object* v_l_320_; lean_object* v_r_321_; lean_object* v___x_322_; lean_object* v_a_323_; 
v_k_318_ = lean_ctor_get(v_x_312_, 1);
v_v_319_ = lean_ctor_get(v_x_312_, 2);
v_l_320_ = lean_ctor_get(v_x_312_, 3);
v_r_321_ = lean_ctor_get(v_x_312_, 4);
v___x_322_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_310_, v_init_311_, v_l_320_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
if (lean_obj_tag(v_a_323_) == 0)
{
lean_object* v_a_324_; 
lean_dec_ref(v___x_322_);
v_a_324_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v_a_323_, 1);
v_d_315_ = v_a_324_;
goto v___jp_314_;
}
else
{
lean_object* v_a_325_; uint8_t v___x_326_; 
v_a_325_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v_a_323_, 1);
v___x_326_ = lean_nat_dec_lt(v_threshold_310_, v_v_319_);
if (v___x_326_ == 0)
{
lean_object* v_a_327_; 
lean_dec(v_a_325_);
v_a_327_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v___x_322_);
if (lean_obj_tag(v_a_327_) == 0)
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v_a_327_, 1);
v_d_315_ = v_a_328_;
goto v___jp_314_;
}
else
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_a_327_, 1);
v_init_311_ = v_a_329_;
v_x_312_ = v_r_321_;
goto _start;
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v___x_322_);
lean_inc(v_v_319_);
lean_inc(v_k_318_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_k_318_);
lean_ctor_set(v___x_331_, 1, v_v_319_);
v___x_332_ = lean_array_push(v_a_325_, v___x_331_);
v_init_311_ = v___x_332_;
v_x_312_ = v_r_321_;
goto _start;
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v_init_311_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
v___jp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v_d_315_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(lean_object* v_threshold_336_, lean_object* v_init_337_, lean_object* v_x_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_336_, v_init_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec(v_threshold_336_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(lean_object* v_hi_341_, lean_object* v_pivot_342_, lean_object* v_as_343_, lean_object* v_i_344_, lean_object* v_k_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_lt(v_k_345_, v_hi_341_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_k_345_);
v___x_347_ = lean_array_fswap(v_as_343_, v_i_344_, v_hi_341_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_i_344_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_snd_349_; lean_object* v___x_350_; lean_object* v_snd_351_; uint8_t v___x_352_; 
v_snd_349_ = lean_ctor_get(v_pivot_342_, 1);
v___x_350_ = lean_array_fget_borrowed(v_as_343_, v_k_345_);
v_snd_351_ = lean_ctor_get(v___x_350_, 1);
v___x_352_ = lean_nat_dec_lt(v_snd_349_, v_snd_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_k_345_, v___x_353_);
lean_dec(v_k_345_);
v_k_345_ = v___x_354_;
goto _start;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_356_ = lean_array_fswap(v_as_343_, v_i_344_, v_k_345_);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v_i_344_, v___x_357_);
lean_dec(v_i_344_);
v___x_359_ = lean_nat_add(v_k_345_, v___x_357_);
lean_dec(v_k_345_);
v_as_343_ = v___x_356_;
v_i_344_ = v___x_358_;
v_k_345_ = v___x_359_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_361_, lean_object* v_pivot_362_, lean_object* v_as_363_, lean_object* v_i_364_, lean_object* v_k_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_361_, v_pivot_362_, v_as_363_, v_i_364_, v_k_365_);
lean_dec_ref(v_pivot_362_);
lean_dec(v_hi_361_);
return v_res_366_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(lean_object* v_a_367_, lean_object* v_b_368_){
_start:
{
lean_object* v_snd_369_; lean_object* v_snd_370_; uint8_t v___x_371_; 
v_snd_369_ = lean_ctor_get(v_b_368_, 1);
v_snd_370_ = lean_ctor_get(v_a_367_, 1);
v___x_371_ = lean_nat_dec_lt(v_snd_369_, v_snd_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(lean_object* v_a_372_, lean_object* v_b_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_372_, v_b_373_);
lean_dec_ref(v_b_373_);
lean_dec_ref(v_a_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(lean_object* v_n_376_, lean_object* v_as_377_, lean_object* v_lo_378_, lean_object* v_hi_379_){
_start:
{
lean_object* v___y_381_; uint8_t v___x_391_; 
v___x_391_ = lean_nat_dec_lt(v_lo_378_, v_hi_379_);
if (v___x_391_ == 0)
{
lean_dec(v_lo_378_);
return v_as_377_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_mid_394_; lean_object* v___y_396_; lean_object* v___y_402_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_392_ = lean_nat_add(v_lo_378_, v_hi_379_);
v___x_393_ = lean_unsigned_to_nat(1u);
v_mid_394_ = lean_nat_shiftr(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
v___x_407_ = lean_array_fget_borrowed(v_as_377_, v_mid_394_);
v___x_408_ = lean_array_fget_borrowed(v_as_377_, v_lo_378_);
v___x_409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
v___y_402_ = v_as_377_;
goto v___jp_401_;
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_array_fswap(v_as_377_, v_lo_378_, v_mid_394_);
v___y_402_ = v___x_410_;
goto v___jp_401_;
}
v___jp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = lean_array_fget_borrowed(v___y_396_, v_mid_394_);
v___x_398_ = lean_array_fget_borrowed(v___y_396_, v_hi_379_);
v___x_399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec(v_mid_394_);
v___y_381_ = v___y_396_;
goto v___jp_380_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_array_fswap(v___y_396_, v_mid_394_, v_hi_379_);
lean_dec(v_mid_394_);
v___y_381_ = v___x_400_;
goto v___jp_380_;
}
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_array_fget_borrowed(v___y_402_, v_hi_379_);
v___x_404_ = lean_array_fget_borrowed(v___y_402_, v_lo_378_);
v___x_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
v___y_396_ = v___y_402_;
goto v___jp_395_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_array_fswap(v___y_402_, v_lo_378_, v_hi_379_);
v___y_396_ = v___x_406_;
goto v___jp_395_;
}
}
}
v___jp_380_:
{
lean_object* v_pivot_382_; lean_object* v___x_383_; lean_object* v_fst_384_; lean_object* v_snd_385_; uint8_t v___x_386_; 
v_pivot_382_ = lean_array_fget(v___y_381_, v_hi_379_);
lean_inc_n(v_lo_378_, 2);
v___x_383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_379_, v_pivot_382_, v___y_381_, v_lo_378_, v_lo_378_);
lean_dec(v_pivot_382_);
v_fst_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_fst_384_);
v_snd_385_ = lean_ctor_get(v___x_383_, 1);
lean_inc(v_snd_385_);
lean_dec_ref(v___x_383_);
v___x_386_ = lean_nat_dec_le(v_hi_379_, v_fst_384_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_376_, v_snd_385_, v_lo_378_, v_fst_384_);
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_add(v_fst_384_, v___x_388_);
lean_dec(v_fst_384_);
v_as_377_ = v___x_387_;
v_lo_378_ = v___x_389_;
goto _start;
}
else
{
lean_dec(v_fst_384_);
lean_dec(v_lo_378_);
return v_snd_385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(lean_object* v_n_411_, lean_object* v_as_412_, lean_object* v_lo_413_, lean_object* v_hi_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_411_, v_as_412_, v_lo_413_, v_hi_414_);
lean_dec(v_hi_414_);
lean_dec(v_n_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps(lean_object* v_e_418_, lean_object* v_threshold_419_){
_start:
{
lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_435_; lean_object* v_a_436_; lean_object* v_counters_443_; lean_object* v_result_444_; lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_counters_443_ = l_Lean_Expr_NumApps_main(v_e_418_);
v_result_444_ = ((lean_object*)(l_Lean_Expr_numApps___closed__0));
v___x_445_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_419_, v_result_444_, v_counters_443_);
lean_dec(v_counters_443_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v___jp_421_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v___y_422_, v___y_424_, v___y_423_, v___y_425_);
lean_dec(v___y_425_);
lean_dec(v___y_422_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
v___jp_428_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_le(v___y_432_, v___y_430_);
if (v___x_433_ == 0)
{
lean_dec(v___y_430_);
lean_inc(v___y_432_);
v___y_422_ = v___y_429_;
v___y_423_ = v___y_432_;
v___y_424_ = v___y_431_;
v___y_425_ = v___y_432_;
goto v___jp_421_;
}
else
{
v___y_422_ = v___y_429_;
v___y_423_ = v___y_432_;
v___y_424_ = v___y_431_;
v___y_425_ = v___y_430_;
goto v___jp_421_;
}
}
v___jp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_array_get_size(v_a_436_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
lean_dec_ref(v___y_435_);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_sub(v___x_437_, v___x_440_);
v___x_442_ = lean_nat_dec_le(v___x_438_, v___x_441_);
if (v___x_442_ == 0)
{
lean_inc(v___x_441_);
v___y_429_ = v___x_437_;
v___y_430_ = v___x_441_;
v___y_431_ = v_a_436_;
v___y_432_ = v___x_441_;
goto v___jp_428_;
}
else
{
v___y_429_ = v___x_437_;
v___y_430_ = v___x_441_;
v___y_431_ = v_a_436_;
v___y_432_ = v___x_438_;
goto v___jp_428_;
}
}
else
{
lean_dec_ref(v_a_436_);
return v___y_435_;
}
}
v_resetjp_447_:
{
lean_object* v_a_450_; lean_object* v___x_452_; 
v_a_450_ = lean_ctor_get(v_a_446_, 0);
lean_inc_n(v_a_450_, 2);
lean_dec(v_a_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_a_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
v___y_435_ = v___x_452_;
v_a_436_ = v_a_450_;
goto v___jp_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps___boxed(lean_object* v_e_455_, lean_object* v_threshold_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Expr_numApps(v_e_455_, v_threshold_456_);
lean_dec(v_threshold_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(lean_object* v_n_459_, lean_object* v_as_460_, lean_object* v_lo_461_, lean_object* v_hi_462_, lean_object* v_w_463_, lean_object* v_hlo_464_, lean_object* v_hhi_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_459_, v_as_460_, v_lo_461_, v_hi_462_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(lean_object* v_n_467_, lean_object* v_as_468_, lean_object* v_lo_469_, lean_object* v_hi_470_, lean_object* v_w_471_, lean_object* v_hlo_472_, lean_object* v_hhi_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(v_n_467_, v_as_468_, v_lo_469_, v_hi_470_, v_w_471_, v_hlo_472_, v_hhi_473_);
lean_dec(v_hi_470_);
lean_dec(v_n_467_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(lean_object* v_n_475_, lean_object* v_lo_476_, lean_object* v_hi_477_, lean_object* v_hhi_478_, lean_object* v_pivot_479_, lean_object* v_as_480_, lean_object* v_i_481_, lean_object* v_k_482_, lean_object* v_ilo_483_, lean_object* v_ik_484_, lean_object* v_w_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_477_, v_pivot_479_, v_as_480_, v_i_481_, v_k_482_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(lean_object* v_n_487_, lean_object* v_lo_488_, lean_object* v_hi_489_, lean_object* v_hhi_490_, lean_object* v_pivot_491_, lean_object* v_as_492_, lean_object* v_i_493_, lean_object* v_k_494_, lean_object* v_ilo_495_, lean_object* v_ik_496_, lean_object* v_w_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(v_n_487_, v_lo_488_, v_hi_489_, v_hhi_490_, v_pivot_491_, v_as_492_, v_i_493_, v_k_494_, v_ilo_495_, v_ik_496_, v_w_497_);
lean_dec_ref(v_pivot_491_);
lean_dec(v_hi_489_);
lean_dec(v_lo_488_);
lean_dec(v_n_487_);
return v_res_498_;
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
