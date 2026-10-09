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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(lean_object* v_a_53_, lean_object* v_x_54_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_53_ = stack[0].m_obj;
lean_object* v_x_54_ = stack[1].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_53_, v_x_54_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec_ref(v_a_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(lean_object* v_m_67_, lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
lean_object* v_size_70_; lean_object* v_buckets_71_; lean_object* v___x_72_; size_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v_fold_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v_bkt_88_; uint8_t v___x_89_; 
v_size_70_ = lean_ctor_get(v_m_67_, 0);
v_buckets_71_ = lean_ctor_get(v_m_67_, 1);
v___x_72_ = lean_array_get_size(v_buckets_71_);
v___x_73_ = lean_ptr_addr(v_a_68_);
v___x_74_ = lean_usize_to_uint64(v___x_73_);
v___x_75_ = 11ULL;
v___x_76_ = lean_uint64_mix_hash(v___x_74_, v___x_75_);
v___x_77_ = 32ULL;
v___x_78_ = lean_uint64_shift_right(v___x_76_, v___x_77_);
v_fold_79_ = lean_uint64_xor(v___x_76_, v___x_78_);
v___x_80_ = 16ULL;
v___x_81_ = lean_uint64_shift_right(v_fold_79_, v___x_80_);
v___x_82_ = lean_uint64_xor(v_fold_79_, v___x_81_);
v___x_83_ = lean_uint64_to_usize(v___x_82_);
v___x_84_ = lean_usize_of_nat(v___x_72_);
v___x_85_ = ((size_t)1ULL);
v___x_86_ = lean_usize_sub(v___x_84_, v___x_85_);
v___x_87_ = lean_usize_land(v___x_83_, v___x_86_);
v_bkt_88_ = lean_array_uget_borrowed(v_buckets_71_, v___x_87_);
v___x_89_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_68_, v_bkt_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_110_; 
lean_inc_ref(v_buckets_71_);
lean_inc(v_size_70_);
v_isSharedCheck_110_ = !lean_is_exclusive(v_m_67_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_111_ = lean_ctor_get(v_m_67_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_m_67_, 0);
lean_dec(v_unused_112_);
v___x_91_ = v_m_67_;
v_isShared_92_ = v_isSharedCheck_110_;
goto v_resetjp_90_;
}
else
{
lean_dec(v_m_67_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_110_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v_size_x27_94_; lean_object* v___x_95_; lean_object* v_buckets_x27_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v_size_x27_94_ = lean_nat_add(v_size_70_, v___x_93_);
lean_dec(v_size_70_);
lean_inc(v_bkt_88_);
v___x_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_95_, 0, v_a_68_);
lean_ctor_set(v___x_95_, 1, v_b_69_);
lean_ctor_set(v___x_95_, 2, v_bkt_88_);
v_buckets_x27_96_ = lean_array_uset(v_buckets_71_, v___x_87_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(4u);
v___x_98_ = lean_nat_mul(v_size_x27_94_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(3u);
v___x_100_ = lean_nat_div(v___x_98_, v___x_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_array_get_size(v_buckets_x27_96_);
v___x_102_ = lean_nat_dec_le(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
if (v___x_102_ == 0)
{
lean_object* v_val_103_; lean_object* v___x_105_; 
v_val_103_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_buckets_x27_96_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_val_103_);
lean_ctor_set(v___x_91_, 0, v_size_x27_94_);
v___x_105_ = v___x_91_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_size_x27_94_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_val_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
else
{
lean_object* v___x_108_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_buckets_x27_96_);
lean_ctor_set(v___x_91_, 0, v_size_x27_94_);
v___x_108_ = v___x_91_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_size_x27_94_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_buckets_x27_96_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
else
{
lean_dec(v_b_69_);
lean_dec_ref(v_a_68_);
return v_m_67_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(lean_object* v_m_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_buckets_115_; lean_object* v___x_116_; size_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_buckets_115_ = lean_ctor_get(v_m_113_, 1);
v___x_116_ = lean_array_get_size(v_buckets_115_);
v___x_117_ = lean_ptr_addr(v_a_114_);
v___x_118_ = lean_usize_to_uint64(v___x_117_);
v___x_119_ = 11ULL;
v___x_120_ = lean_uint64_mix_hash(v___x_118_, v___x_119_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_116_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v___x_132_ = lean_array_uget_borrowed(v_buckets_115_, v___x_131_);
v___x_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_114_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_113_ = stack[0].m_obj;
lean_object* v_a_114_ = stack[1].m_obj;
uint8_t v_res_134_;
v_res_134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_113_, v_a_114_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(lean_object* v_m_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_135_, v_a_136_);
lean_dec_ref(v_a_136_);
lean_dec_ref(v_m_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_visit___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v_dummy_140_; 
v___x_139_ = lean_box(0);
v_dummy_140_ = l_Lean_Expr_sort___override(v___x_139_);
return v_dummy_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___y_146_; 
if (lean_obj_tag(v_x_141_) == 5)
{
lean_object* v_fn_171_; lean_object* v_arg_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_fn_171_ = lean_ctor_get(v_x_141_, 0);
lean_inc_ref(v_fn_171_);
v_arg_172_ = lean_ctor_get(v_x_141_, 1);
lean_inc_ref(v_arg_172_);
lean_dec_ref_known(v_x_141_, 2);
v___x_173_ = lean_array_set(v_x_142_, v_x_143_, v_arg_172_);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_sub(v_x_143_, v___x_174_);
lean_dec(v_x_143_);
v_x_141_ = v_fn_171_;
v_x_142_ = v___x_173_;
v_x_143_ = v___x_175_;
goto _start;
}
else
{
lean_dec(v_x_143_);
if (lean_obj_tag(v_x_141_) == 4)
{
lean_object* v_declName_177_; lean_object* v_visited_178_; lean_object* v_counters_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_194_; 
v_declName_177_ = lean_ctor_get(v_x_141_, 0);
v_visited_178_ = lean_ctor_get(v___y_144_, 0);
v_counters_179_ = lean_ctor_get(v___y_144_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v___y_144_);
if (v_isSharedCheck_194_ == 0)
{
v___x_181_ = v___y_144_;
v_isShared_182_ = v_isSharedCheck_194_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_counters_179_);
lean_inc(v_visited_178_);
lean_dec(v___y_144_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_194_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___y_184_; lean_object* v___x_191_; 
v___x_191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_counters_179_, v_declName_177_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_object* v_val_193_; 
v_val_193_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_191_, 1);
v___y_184_ = v_val_193_;
goto v___jp_183_;
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v___y_184_, v___x_185_);
lean_dec(v___y_184_);
lean_inc(v_declName_177_);
v___x_187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_177_, v___x_186_, v_counters_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_187_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_visited_178_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v___y_146_ = v___x_189_;
goto v___jp_145_;
}
}
}
}
else
{
v___y_146_ = v___y_144_;
goto v___jp_145_;
}
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v_snd_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_169_; 
v___x_147_ = l_Lean_Expr_NumApps_visit(v_x_141_, v___y_146_);
v_snd_148_ = lean_ctor_get(v___x_147_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v___x_147_, 0);
lean_dec(v_unused_170_);
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_169_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_snd_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_169_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_array_get_size(v_x_142_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_nat_dec_lt(v___x_152_, v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref(v_x_142_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_154_);
v___x_157_ = v___x_150_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_snd_148_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_le(v___x_153_, v___x_153_);
if (v___x_159_ == 0)
{
if (v___x_155_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v_x_142_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_154_);
v___x_161_ = v___x_150_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_snd_148_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
else
{
size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; 
lean_del_object(v___x_150_);
v___x_163_ = ((size_t)0ULL);
v___x_164_ = lean_usize_of_nat(v___x_153_);
v___x_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_142_, v___x_163_, v___x_164_, v___x_154_, v_snd_148_);
lean_dec_ref(v_x_142_);
return v___x_165_;
}
}
else
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
lean_del_object(v___x_150_);
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_153_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_142_, v___x_166_, v___x_167_, v___x_154_, v_snd_148_);
lean_dec_ref(v_x_142_);
return v___x_168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_visit(lean_object* v_e_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_d_198_; lean_object* v_b_199_; lean_object* v___y_200_; lean_object* v_visited_204_; lean_object* v_counters_205_; uint8_t v___x_206_; 
v_visited_204_ = lean_ctor_get(v_a_196_, 0);
v_counters_205_ = lean_ctor_get(v_a_196_, 1);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_visited_204_, v_e_195_);
if (v___x_206_ == 0)
{
lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_238_; 
lean_inc(v_counters_205_);
lean_inc_ref(v_visited_204_);
v_isSharedCheck_238_ = !lean_is_exclusive(v_a_196_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; lean_object* v_unused_240_; 
v_unused_239_ = lean_ctor_get(v_a_196_, 1);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_a_196_, 0);
lean_dec(v_unused_240_);
v___x_208_ = v_a_196_;
v_isShared_209_ = v_isSharedCheck_238_;
goto v_resetjp_207_;
}
else
{
lean_dec(v_a_196_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_238_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = lean_box(0);
lean_inc_ref(v_e_195_);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_visited_204_, v_e_195_, v___x_210_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_counters_205_);
v___x_213_ = v_reuseFailAlloc_237_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
switch(lean_obj_tag(v_e_195_))
{
case 7:
{
lean_object* v_binderType_214_; lean_object* v_body_215_; 
v_binderType_214_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_binderType_214_);
v_body_215_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref(v_body_215_);
lean_dec_ref_known(v_e_195_, 3);
v_d_198_ = v_binderType_214_;
v_b_199_ = v_body_215_;
v___y_200_ = v___x_213_;
goto v___jp_197_;
}
case 6:
{
lean_object* v_binderType_216_; lean_object* v_body_217_; 
v_binderType_216_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_binderType_216_);
v_body_217_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref(v_body_217_);
lean_dec_ref_known(v_e_195_, 3);
v_d_198_ = v_binderType_216_;
v_b_199_ = v_body_217_;
v___y_200_ = v___x_213_;
goto v___jp_197_;
}
case 10:
{
lean_object* v_expr_218_; 
v_expr_218_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_expr_218_);
lean_dec_ref_known(v_e_195_, 2);
v_e_195_ = v_expr_218_;
v_a_196_ = v___x_213_;
goto _start;
}
case 8:
{
lean_object* v_type_220_; lean_object* v_value_221_; lean_object* v_body_222_; lean_object* v___x_223_; lean_object* v_snd_224_; lean_object* v___x_225_; lean_object* v_snd_226_; 
v_type_220_ = lean_ctor_get(v_e_195_, 1);
lean_inc_ref(v_type_220_);
v_value_221_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref(v_value_221_);
v_body_222_ = lean_ctor_get(v_e_195_, 3);
lean_inc_ref(v_body_222_);
lean_dec_ref_known(v_e_195_, 4);
v___x_223_ = l_Lean_Expr_NumApps_visit(v_type_220_, v___x_213_);
v_snd_224_ = lean_ctor_get(v___x_223_, 1);
lean_inc(v_snd_224_);
lean_dec_ref(v___x_223_);
v___x_225_ = l_Lean_Expr_NumApps_visit(v_value_221_, v_snd_224_);
v_snd_226_ = lean_ctor_get(v___x_225_, 1);
lean_inc(v_snd_226_);
lean_dec_ref(v___x_225_);
v_e_195_ = v_body_222_;
v_a_196_ = v_snd_226_;
goto _start;
}
case 5:
{
lean_object* v_dummy_228_; lean_object* v_nargs_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_dummy_228_ = lean_obj_once(&l_Lean_Expr_NumApps_visit___closed__0, &l_Lean_Expr_NumApps_visit___closed__0_once, _init_l_Lean_Expr_NumApps_visit___closed__0);
v_nargs_229_ = l_Lean_Expr_getAppNumArgs(v_e_195_);
lean_inc(v_nargs_229_);
v___x_230_ = lean_mk_array(v_nargs_229_, v_dummy_228_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_sub(v_nargs_229_, v___x_231_);
lean_dec(v_nargs_229_);
v___x_233_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(v_e_195_, v___x_230_, v___x_232_, v___x_213_);
return v___x_233_;
}
case 11:
{
lean_object* v_struct_234_; 
v_struct_234_ = lean_ctor_get(v_e_195_, 2);
lean_inc_ref(v_struct_234_);
lean_dec_ref_known(v_e_195_, 3);
v_e_195_ = v_struct_234_;
v_a_196_ = v___x_213_;
goto _start;
}
default: 
{
lean_object* v___x_236_; 
lean_dec_ref(v_e_195_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_210_);
lean_ctor_set(v___x_236_, 1, v___x_213_);
return v___x_236_;
}
}
}
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref(v_e_195_);
v___x_241_ = lean_box(0);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_a_196_);
return v___x_242_;
}
v___jp_197_:
{
lean_object* v___x_201_; lean_object* v_snd_202_; 
v___x_201_ = l_Lean_Expr_NumApps_visit(v_d_198_, v___y_200_);
v_snd_202_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_snd_202_);
lean_dec_ref(v___x_201_);
v_e_195_ = v_b_199_;
v_a_196_ = v_snd_202_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(lean_object* v_as_243_, size_t v_i_244_, size_t v_stop_245_, lean_object* v_b_246_, lean_object* v___y_247_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_usize_dec_eq(v_i_244_, v_stop_245_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_fst_251_; lean_object* v_snd_252_; size_t v___x_253_; size_t v___x_254_; 
v___x_249_ = lean_array_uget_borrowed(v_as_243_, v_i_244_);
lean_inc(v___x_249_);
v___x_250_ = l_Lean_Expr_NumApps_visit(v___x_249_, v___y_247_);
v_fst_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_fst_251_);
v_snd_252_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_snd_252_);
lean_dec_ref(v___x_250_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_add(v_i_244_, v___x_253_);
v_i_244_ = v___x_254_;
v_b_246_ = v_fst_251_;
v___y_247_ = v_snd_252_;
goto _start;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_b_246_);
lean_ctor_set(v___x_256_, 1, v___y_247_);
return v___x_256_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_243_ = stack[0].m_obj;
size_t v_i_244_ = stack[1].m_num;
size_t v_stop_245_ = stack[2].m_num;
lean_object* v_b_246_ = stack[3].m_obj;
lean_object* v___y_247_ = stack[4].m_obj;
lean_object* v_res_257_;
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_243_, v_i_244_, v_stop_245_, v_b_246_, v___y_247_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(lean_object* v_as_258_, lean_object* v_i_259_, lean_object* v_stop_260_, lean_object* v_b_261_, lean_object* v___y_262_){
_start:
{
size_t v_i_boxed_263_; size_t v_stop_boxed_264_; lean_object* v_res_265_; 
v_i_boxed_263_ = lean_unbox_usize(v_i_259_);
lean_dec(v_i_259_);
v_stop_boxed_264_ = lean_unbox_usize(v_stop_260_);
lean_dec(v_stop_260_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_258_, v_i_boxed_263_, v_stop_boxed_264_, v_b_261_, v___y_262_);
lean_dec_ref(v_as_258_);
return v_res_265_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_267_ = stack[1].m_obj;
lean_object* v_a_268_ = stack[2].m_obj;
uint8_t v_res_270_;
v_res_270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(lean_box(0), v_m_267_, v_a_268_);
stack->m_num = v_res_270_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(lean_object* v_00_u03b2_271_, lean_object* v_m_272_, lean_object* v_a_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(v_00_u03b2_271_, v_m_272_, v_a_273_);
lean_dec_ref(v_a_273_);
lean_dec_ref(v_m_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2(lean_object* v_00_u03b2_276_, lean_object* v_m_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_m_277_, v_a_278_, v_b_279_);
return v___x_280_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_object* v_00_u03b2_281_, lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_282_, v_x_283_);
return v___x_284_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_282_ = stack[1].m_obj;
lean_object* v_x_283_ = stack[2].m_obj;
uint8_t v_res_285_;
v_res_285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(lean_box(0), v_a_282_, v_x_283_);
stack->m_num = v_res_285_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_286_, lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(v_00_u03b2_286_, v_a_287_, v_x_288_);
lean_dec(v_x_288_);
lean_dec_ref(v_a_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3(lean_object* v_00_u03b2_291_, lean_object* v_data_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_data_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_294_, lean_object* v_i_295_, lean_object* v_source_296_, lean_object* v_target_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v_i_295_, v_source_296_, v_target_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_300_, v_x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__0(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(64u);
v___x_304_ = l_Lean_mkPtrSet___redArg(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Expr_NumApps_main___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(1);
v___x_306_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__0, &l_Lean_Expr_NumApps_main___closed__0_once, _init_l_Lean_Expr_NumApps_main___closed__0);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_NumApps_main(lean_object* v_e_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v_snd_311_; lean_object* v_counters_312_; 
v___x_309_ = lean_obj_once(&l_Lean_Expr_NumApps_main___closed__1, &l_Lean_Expr_NumApps_main___closed__1_once, _init_l_Lean_Expr_NumApps_main___closed__1);
v___x_310_ = l_Lean_Expr_NumApps_visit(v_e_308_, v___x_309_);
v_snd_311_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_snd_311_);
lean_dec_ref(v___x_310_);
v_counters_312_ = lean_ctor_get(v_snd_311_, 1);
lean_inc(v_counters_312_);
lean_dec(v_snd_311_);
return v_counters_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(lean_object* v_e_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Expr_NumApps_main(v_e_313_);
return v___x_314_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(lean_object* v_threshold_315_, lean_object* v_init_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_d_320_; 
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_l_325_; lean_object* v_r_326_; lean_object* v___x_327_; lean_object* v_a_328_; 
v_k_323_ = lean_ctor_get(v_x_317_, 1);
v_v_324_ = lean_ctor_get(v_x_317_, 2);
v_l_325_ = lean_ctor_get(v_x_317_, 3);
v_r_326_ = lean_ctor_get(v_x_317_, 4);
v___x_327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_315_, v_init_316_, v_l_325_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
if (lean_obj_tag(v_a_328_) == 0)
{
lean_object* v_a_329_; 
lean_inc_ref(v_a_328_);
lean_dec_ref(v___x_327_);
v_a_329_ = lean_ctor_get(v_a_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_a_328_, 1);
v_d_320_ = v_a_329_;
goto v___jp_319_;
}
else
{
lean_object* v_a_330_; uint8_t v___x_331_; 
v_a_330_ = lean_ctor_get(v_a_328_, 0);
v___x_331_ = lean_nat_dec_lt(v_threshold_315_, v_v_324_);
if (v___x_331_ == 0)
{
lean_object* v_a_332_; 
v_a_332_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_327_);
if (lean_obj_tag(v_a_332_) == 0)
{
lean_object* v_a_333_; 
v_a_333_ = lean_ctor_get(v_a_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v_a_332_, 1);
v_d_320_ = v_a_333_;
goto v___jp_319_;
}
else
{
lean_object* v_a_334_; 
v_a_334_ = lean_ctor_get(v_a_332_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v_a_332_, 1);
v_init_316_ = v_a_334_;
v_x_317_ = v_r_326_;
goto _start;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_inc(v_a_330_);
lean_dec_ref(v___x_327_);
lean_inc(v_v_324_);
lean_inc(v_k_323_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_k_323_);
lean_ctor_set(v___x_336_, 1, v_v_324_);
v___x_337_ = lean_array_push(v_a_330_, v___x_336_);
v_init_316_ = v___x_337_;
v_x_317_ = v_r_326_;
goto _start;
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_init_316_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_d_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_threshold_315_ = stack[0].m_obj;
lean_object* v_init_316_ = stack[1].m_obj;
lean_object* v_x_317_ = stack[2].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_315_, v_init_316_, v_x_317_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(lean_object* v_threshold_342_, lean_object* v_init_343_, lean_object* v_x_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_342_, v_init_343_, v_x_344_);
lean_dec(v_x_344_);
lean_dec(v_threshold_342_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(lean_object* v_hi_347_, lean_object* v_pivot_348_, lean_object* v_as_349_, lean_object* v_i_350_, lean_object* v_k_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_lt(v_k_351_, v_hi_347_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_k_351_);
v___x_353_ = lean_array_fswap(v_as_349_, v_i_350_, v_hi_347_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_i_350_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
else
{
lean_object* v_snd_355_; lean_object* v___x_356_; lean_object* v_snd_357_; uint8_t v___x_358_; 
v_snd_355_ = lean_ctor_get(v_pivot_348_, 1);
v___x_356_ = lean_array_fget_borrowed(v_as_349_, v_k_351_);
v_snd_357_ = lean_ctor_get(v___x_356_, 1);
v___x_358_ = lean_nat_dec_lt(v_snd_355_, v_snd_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_k_351_, v___x_359_);
lean_dec(v_k_351_);
v_k_351_ = v___x_360_;
goto _start;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_array_fswap(v_as_349_, v_i_350_, v_k_351_);
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_i_350_, v___x_363_);
lean_dec(v_i_350_);
v___x_365_ = lean_nat_add(v_k_351_, v___x_363_);
lean_dec(v_k_351_);
v_as_349_ = v___x_362_;
v_i_350_ = v___x_364_;
v_k_351_ = v___x_365_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(lean_object* v_hi_367_, lean_object* v_pivot_368_, lean_object* v_as_369_, lean_object* v_i_370_, lean_object* v_k_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_367_, v_pivot_368_, v_as_369_, v_i_370_, v_k_371_);
lean_dec_ref(v_pivot_368_);
lean_dec(v_hi_367_);
return v_res_372_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(lean_object* v_a_373_, lean_object* v_b_374_){
_start:
{
lean_object* v_snd_375_; lean_object* v_snd_376_; uint8_t v___x_377_; 
v_snd_375_ = lean_ctor_get(v_b_374_, 1);
v_snd_376_ = lean_ctor_get(v_a_373_, 1);
v___x_377_ = lean_nat_dec_lt(v_snd_375_, v_snd_376_);
return v___x_377_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_373_ = stack[0].m_obj;
lean_object* v_b_374_ = stack[1].m_obj;
uint8_t v_res_378_;
v_res_378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_373_, v_b_374_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_379_, v_b_380_);
lean_dec_ref(v_b_380_);
lean_dec_ref(v_a_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(lean_object* v_n_383_, lean_object* v_as_384_, lean_object* v_lo_385_, lean_object* v_hi_386_){
_start:
{
lean_object* v___y_388_; uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_lt(v_lo_385_, v_hi_386_);
if (v___x_398_ == 0)
{
lean_dec(v_lo_385_);
return v_as_384_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_mid_401_; lean_object* v___y_403_; lean_object* v___y_409_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_399_ = lean_nat_add(v_lo_385_, v_hi_386_);
v___x_400_ = lean_unsigned_to_nat(1u);
v_mid_401_ = lean_nat_shiftr(v___x_399_, v___x_400_);
lean_dec(v___x_399_);
v___x_414_ = lean_array_fget_borrowed(v_as_384_, v_mid_401_);
v___x_415_ = lean_array_fget_borrowed(v_as_384_, v_lo_385_);
v___x_416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
v___y_409_ = v_as_384_;
goto v___jp_408_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_array_fswap(v_as_384_, v_lo_385_, v_mid_401_);
v___y_409_ = v___x_417_;
goto v___jp_408_;
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_array_fget_borrowed(v___y_403_, v_mid_401_);
v___x_405_ = lean_array_fget_borrowed(v___y_403_, v_hi_386_);
v___x_406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v_mid_401_);
v___y_388_ = v___y_403_;
goto v___jp_387_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_array_fswap(v___y_403_, v_mid_401_, v_hi_386_);
lean_dec(v_mid_401_);
v___y_388_ = v___x_407_;
goto v___jp_387_;
}
}
v___jp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_array_fget_borrowed(v___y_409_, v_hi_386_);
v___x_411_ = lean_array_fget_borrowed(v___y_409_, v_lo_385_);
v___x_412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
v___y_403_ = v___y_409_;
goto v___jp_402_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_array_fswap(v___y_409_, v_lo_385_, v_hi_386_);
v___y_403_ = v___x_413_;
goto v___jp_402_;
}
}
}
v___jp_387_:
{
lean_object* v_pivot_389_; lean_object* v___x_390_; lean_object* v_fst_391_; lean_object* v_snd_392_; uint8_t v___x_393_; 
v_pivot_389_ = lean_array_fget(v___y_388_, v_hi_386_);
lean_inc_n(v_lo_385_, 2);
v___x_390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_386_, v_pivot_389_, v___y_388_, v_lo_385_, v_lo_385_);
lean_dec(v_pivot_389_);
v_fst_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v___x_390_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v___x_390_);
v___x_393_ = lean_nat_dec_le(v_hi_386_, v_fst_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_383_, v_snd_392_, v_lo_385_, v_fst_391_);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_fst_391_, v___x_395_);
lean_dec(v_fst_391_);
v_as_384_ = v___x_394_;
v_lo_385_ = v___x_396_;
goto _start;
}
else
{
lean_dec(v_fst_391_);
lean_dec(v_lo_385_);
return v_snd_392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(lean_object* v_n_418_, lean_object* v_as_419_, lean_object* v_lo_420_, lean_object* v_hi_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_418_, v_as_419_, v_lo_420_, v_hi_421_);
lean_dec(v_hi_421_);
lean_dec(v_n_418_);
return v_res_422_;
}
}
lean_object* l_Lean_Expr_numApps(lean_object* v_e_425_, lean_object* v_threshold_426_){
_start:
{
lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_442_; lean_object* v_a_443_; lean_object* v_counters_450_; lean_object* v_result_451_; lean_object* v___x_452_; lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
v_counters_450_ = l_Lean_Expr_NumApps_main(v_e_425_);
v_result_451_ = ((lean_object*)(l_Lean_Expr_numApps___closed__0));
v___x_452_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(v_threshold_426_, v_result_451_, v_counters_450_);
lean_dec(v_counters_450_);
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v___jp_428_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v___y_430_, v___y_429_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec(v___y_430_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
v___jp_435_:
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_le(v___y_439_, v___y_437_);
if (v___x_440_ == 0)
{
lean_dec(v___y_437_);
lean_inc(v___y_439_);
v___y_429_ = v___y_436_;
v___y_430_ = v___y_438_;
v___y_431_ = v___y_439_;
v___y_432_ = v___y_439_;
goto v___jp_428_;
}
else
{
v___y_429_ = v___y_436_;
v___y_430_ = v___y_438_;
v___y_431_ = v___y_439_;
v___y_432_ = v___y_437_;
goto v___jp_428_;
}
}
v___jp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_array_get_size(v_a_443_);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_nat_dec_eq(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
lean_dec_ref(v___y_442_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v___x_444_, v___x_447_);
v___x_449_ = lean_nat_dec_le(v___x_445_, v___x_448_);
if (v___x_449_ == 0)
{
lean_inc(v___x_448_);
v___y_436_ = v_a_443_;
v___y_437_ = v___x_448_;
v___y_438_ = v___x_444_;
v___y_439_ = v___x_448_;
goto v___jp_435_;
}
else
{
v___y_436_ = v_a_443_;
v___y_437_ = v___x_448_;
v___y_438_ = v___x_444_;
v___y_439_ = v___x_445_;
goto v___jp_435_;
}
}
else
{
lean_dec_ref(v_a_443_);
return v___y_442_;
}
}
v_resetjp_454_:
{
lean_object* v_a_457_; lean_object* v___x_459_; 
v_a_457_ = lean_ctor_get(v_a_453_, 0);
lean_inc_n(v_a_457_, 2);
lean_dec(v_a_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_a_457_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_442_ = v___x_459_;
v_a_443_ = v_a_457_;
goto v___jp_441_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_numApps_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_425_ = stack[0].m_obj;
lean_object* v_threshold_426_ = stack[1].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_Expr_numApps(v_e_425_, v_threshold_426_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_numApps___boxed(lean_object* v_e_463_, lean_object* v_threshold_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Expr_numApps(v_e_463_, v_threshold_464_);
lean_dec(v_threshold_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(lean_object* v_n_467_, lean_object* v_as_468_, lean_object* v_lo_469_, lean_object* v_hi_470_, lean_object* v_w_471_, lean_object* v_hlo_472_, lean_object* v_hhi_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_467_, v_as_468_, v_lo_469_, v_hi_470_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(lean_object* v_n_475_, lean_object* v_as_476_, lean_object* v_lo_477_, lean_object* v_hi_478_, lean_object* v_w_479_, lean_object* v_hlo_480_, lean_object* v_hhi_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(v_n_475_, v_as_476_, v_lo_477_, v_hi_478_, v_w_479_, v_hlo_480_, v_hhi_481_);
lean_dec(v_hi_478_);
lean_dec(v_n_475_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(lean_object* v_n_483_, lean_object* v_lo_484_, lean_object* v_hi_485_, lean_object* v_hhi_486_, lean_object* v_pivot_487_, lean_object* v_as_488_, lean_object* v_i_489_, lean_object* v_k_490_, lean_object* v_ilo_491_, lean_object* v_ik_492_, lean_object* v_w_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_485_, v_pivot_487_, v_as_488_, v_i_489_, v_k_490_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(lean_object* v_n_495_, lean_object* v_lo_496_, lean_object* v_hi_497_, lean_object* v_hhi_498_, lean_object* v_pivot_499_, lean_object* v_as_500_, lean_object* v_i_501_, lean_object* v_k_502_, lean_object* v_ilo_503_, lean_object* v_ik_504_, lean_object* v_w_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(v_n_495_, v_lo_496_, v_hi_497_, v_hhi_498_, v_pivot_499_, v_as_500_, v_i_501_, v_k_502_, v_ilo_503_, v_ik_504_, v_w_505_);
lean_dec_ref(v_pivot_499_);
lean_dec(v_hi_497_);
lean_dec(v_lo_496_);
lean_dec(v_n_495_);
return v_res_506_;
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
