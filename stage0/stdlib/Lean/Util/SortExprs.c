// Lean compiler output
// Module: Lean.Util.SortExprs
// Imports: public import Lean.Expr
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_sortExprs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__0;
static lean_once_cell_t l_Lean_sortExprs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__1;
static lean_once_cell_t l_Lean_sortExprs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__2;
static lean_once_cell_t l_Lean_sortExprs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__3;
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
return v_bs_3_;
}
else
{
lean_object* v_v_5_; lean_object* v___x_6_; lean_object* v_bs_x27_7_; lean_object* v___x_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; lean_object* v___x_12_; 
v_v_5_ = lean_array_uget(v_bs_3_, v_i_2_);
v___x_6_ = lean_unsigned_to_nat(0u);
v_bs_x27_7_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_6_);
v___x_8_ = lean_usize_to_nat(v_i_2_);
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_v_5_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_2_, v___x_10_);
v___x_12_ = lean_array_uset(v_bs_x27_7_, v_i_2_, v___x_9_);
v_i_2_ = v___x_11_;
v_bs_3_ = v___x_12_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object* v_sz_14_, lean_object* v_i_15_, lean_object* v_bs_16_){
_start:
{
size_t v_sz_boxed_17_; size_t v_i_boxed_18_; lean_object* v_res_19_; 
v_sz_boxed_17_ = lean_unbox_usize(v_sz_14_);
lean_dec(v_sz_14_);
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg(v_sz_boxed_17_, v_i_boxed_18_, v_bs_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object* v_m_20_, lean_object* v_query_21_, lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_zero_25_; uint8_t v_isZero_26_; 
v_zero_25_ = lean_unsigned_to_nat(0u);
v_isZero_26_ = lean_nat_dec_eq(v_x_23_, v_zero_25_);
if (v_isZero_26_ == 1)
{
lean_dec(v_x_24_);
lean_dec(v_x_23_);
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(2);
return v___x_27_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_val_28_ = lean_ctor_get(v_x_22_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v_x_22_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_val_28_);
lean_dec(v_x_22_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_val_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
else
{
lean_object* v_keyArray_36_; lean_object* v_valueArray_37_; lean_object* v___x_38_; uint8_t v_isSome_39_; 
v_keyArray_36_ = lean_ctor_get(v_m_20_, 1);
v_valueArray_37_ = lean_ctor_get(v_m_20_, 2);
v___x_38_ = lean_array_fget_borrowed(v_keyArray_36_, v_x_24_);
v_isSome_39_ = lean_noption_is_some(v___x_38_);
if (v_isSome_39_ == 0)
{
lean_dec(v_x_23_);
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v___x_40_; 
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_24_);
return v___x_40_;
}
else
{
lean_object* v_val_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_x_24_);
v_val_41_ = lean_ctor_get(v_x_22_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v_x_22_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_val_41_);
lean_dec(v_x_22_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_val_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
else
{
lean_object* v_one_49_; lean_object* v_n_50_; lean_object* v___y_52_; 
v_one_49_ = lean_unsigned_to_nat(1u);
v_n_50_ = lean_nat_sub(v_x_23_, v_one_49_);
lean_dec(v_x_23_);
if (v_isSome_39_ == 0)
{
goto v___jp_58_;
}
else
{
lean_object* v___x_60_; uint8_t v_isSome_61_; 
v___x_60_ = lean_array_fget_borrowed(v_valueArray_37_, v_x_24_);
v_isSome_61_ = lean_noption_is_some(v___x_60_);
if (v_isSome_61_ == 0)
{
goto v___jp_58_;
}
else
{
lean_object* v_val_62_; uint8_t v___x_63_; 
lean_inc(v___x_38_);
v_val_62_ = lean_noption_get(v___x_38_);
v___x_63_ = lean_nat_dec_eq(v_val_62_, v_query_21_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
lean_dec(v_val_62_);
v___x_64_ = lean_array_get_size(v_keyArray_36_);
v___x_65_ = lean_nat_add(v_x_24_, v_one_49_);
lean_dec(v_x_24_);
v___x_66_ = lean_nat_dec_lt(v___x_65_, v___x_64_);
if (v___x_66_ == 0)
{
lean_dec(v___x_65_);
v_x_23_ = v_n_50_;
v_x_24_ = v_zero_25_;
goto _start;
}
else
{
v_x_23_ = v_n_50_;
v_x_24_ = v___x_65_;
goto _start;
}
}
else
{
lean_object* v_val_69_; lean_object* v___x_70_; 
lean_dec(v_n_50_);
lean_dec(v_x_22_);
lean_inc(v___x_60_);
v_val_69_ = lean_noption_get(v___x_60_);
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v_x_24_);
lean_ctor_set(v___x_70_, 1, v_val_62_);
lean_ctor_set(v___x_70_, 2, v_val_69_);
return v___x_70_;
}
}
}
v___jp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_53_ = lean_array_get_size(v_keyArray_36_);
v___x_54_ = lean_nat_add(v_x_24_, v_one_49_);
lean_dec(v_x_24_);
v___x_55_ = lean_nat_dec_lt(v___x_54_, v___x_53_);
if (v___x_55_ == 0)
{
lean_dec(v___x_54_);
v_x_22_ = v___y_52_;
v_x_23_ = v_n_50_;
v_x_24_ = v_zero_25_;
goto _start;
}
else
{
v_x_22_ = v___y_52_;
v_x_23_ = v_n_50_;
v_x_24_ = v___x_54_;
goto _start;
}
}
v___jp_58_:
{
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v___x_59_; 
lean_inc(v_x_24_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v_x_24_);
v___y_52_ = v___x_59_;
goto v___jp_51_;
}
else
{
v___y_52_ = v_x_22_;
goto v___jp_51_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object* v_m_71_, lean_object* v_query_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_m_71_, v_query_72_, v_x_73_, v_x_74_, v_x_75_);
lean_dec(v_query_72_);
lean_dec_ref(v_m_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_keyArray_79_; lean_object* v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v_fold_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_keyArray_79_ = lean_ctor_get(v_m_77_, 1);
v___x_80_ = lean_array_get_size(v_keyArray_79_);
v___x_81_ = lean_uint64_of_nat(v_query_78_);
v___x_82_ = 32ULL;
v___x_83_ = lean_uint64_shift_right(v___x_81_, v___x_82_);
v_fold_84_ = lean_uint64_xor(v___x_81_, v___x_83_);
v___x_85_ = 16ULL;
v___x_86_ = lean_uint64_shift_right(v_fold_84_, v___x_85_);
v___x_87_ = lean_uint64_xor(v_fold_84_, v___x_86_);
v___x_88_ = lean_uint64_to_usize(v___x_87_);
v___x_89_ = lean_usize_of_nat(v___x_80_);
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_sub(v___x_89_, v___x_90_);
v___x_92_ = lean_usize_land(v___x_88_, v___x_91_);
v___x_93_ = lean_usize_to_nat(v___x_92_);
v___x_94_ = lean_box(0);
v___x_95_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_m_77_, v_query_78_, v___x_94_, v___x_80_, v___x_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg___boxed(lean_object* v_m_96_, lean_object* v_query_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(v_m_96_, v_query_97_);
lean_dec(v_query_97_);
lean_dec_ref(v_m_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg(lean_object* v_b_99_, lean_object* v_acc_100_, lean_object* v_i_101_){
_start:
{
lean_object* v___y_103_; lean_object* v_keyArray_111_; lean_object* v_valueArray_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_keyArray_111_ = lean_ctor_get(v_b_99_, 1);
v_valueArray_112_ = lean_ctor_get(v_b_99_, 2);
v___x_113_ = lean_array_get_size(v_keyArray_111_);
v___x_114_ = lean_nat_dec_lt(v_i_101_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec(v_i_101_);
return v_acc_100_;
}
else
{
lean_object* v___x_115_; uint8_t v_isSome_116_; 
v___x_115_ = lean_array_fget_borrowed(v_keyArray_111_, v_i_101_);
v_isSome_116_ = lean_noption_is_some(v___x_115_);
if (v_isSome_116_ == 0)
{
goto v___jp_107_;
}
else
{
lean_object* v___x_117_; uint8_t v_isSome_118_; 
v___x_117_ = lean_array_fget_borrowed(v_valueArray_112_, v_i_101_);
v_isSome_118_ = lean_noption_is_some(v___x_117_);
if (v_isSome_118_ == 0)
{
goto v___jp_107_;
}
else
{
lean_object* v_val_119_; lean_object* v_val_120_; lean_object* v_i_122_; lean_object* v___x_127_; 
lean_inc(v___x_115_);
v_val_119_ = lean_noption_get(v___x_115_);
lean_inc(v___x_117_);
v_val_120_ = lean_noption_get(v___x_117_);
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(v_acc_100_, v_val_119_);
switch(lean_obj_tag(v___x_127_))
{
case 0:
{
lean_object* v_index_128_; lean_object* v_size_129_; lean_object* v___x_130_; 
v_index_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_index_128_);
lean_dec_ref_known(v___x_127_, 3);
v_size_129_ = lean_ctor_get(v_acc_100_, 0);
lean_inc(v_size_129_);
v___x_130_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_100_, v_size_129_, v_index_128_, v_val_119_, v_val_120_);
lean_dec(v_index_128_);
v___y_103_ = v___x_130_;
goto v___jp_102_;
}
case 1:
{
lean_object* v_index_131_; 
v_index_131_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_index_131_);
lean_dec_ref_known(v___x_127_, 1);
v_i_122_ = v_index_131_;
goto v___jp_121_;
}
default: 
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_100_, v___x_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_index_134_; 
v_index_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_index_134_);
lean_dec_ref_known(v___x_133_, 1);
v_i_122_ = v_index_134_;
goto v___jp_121_;
}
else
{
lean_dec(v_val_120_);
lean_dec(v_val_119_);
v___y_103_ = v_acc_100_;
goto v___jp_102_;
}
}
}
v___jp_121_:
{
lean_object* v_size_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_size_123_ = lean_ctor_get(v_acc_100_, 0);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_size_123_, v___x_124_);
v___x_126_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_100_, v___x_125_, v_i_122_, v_val_119_, v_val_120_);
lean_dec(v_i_122_);
v___y_103_ = v___x_126_;
goto v___jp_102_;
}
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v_i_101_, v___x_104_);
lean_dec(v_i_101_);
v_acc_100_ = v___y_103_;
v_i_101_ = v___x_105_;
goto _start;
}
v___jp_107_:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_i_101_, v___x_108_);
lean_dec(v_i_101_);
v_i_101_ = v___x_109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_135_, lean_object* v_acc_136_, lean_object* v_i_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg(v_b_135_, v_acc_136_, v_i_137_);
lean_dec_ref(v_b_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg(lean_object* v_init_139_, lean_object* v_b_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg(v_b_140_, v_init_139_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg___boxed(lean_object* v_init_143_, lean_object* v_b_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg(v_init_143_, v_b_144_);
lean_dec_ref(v_b_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(lean_object* v_m_146_){
_start:
{
lean_object* v_keyArray_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_cellCount_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_target_154_; lean_object* v___x_155_; 
v_keyArray_147_ = lean_ctor_get(v_m_146_, 1);
v___x_148_ = lean_array_get_size(v_keyArray_147_);
v___x_149_ = lean_unsigned_to_nat(2u);
v_cellCount_150_ = lean_nat_mul(v___x_148_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_150_);
v___x_152_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_150_);
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_150_);
v_target_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_154_, 0, v___x_151_);
lean_ctor_set(v_target_154_, 1, v___x_152_);
lean_ctor_set(v_target_154_, 2, v___x_153_);
v___x_155_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg(v_target_154_, v_m_146_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg___boxed(lean_object* v_m_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(v_m_156_);
lean_dec_ref(v_m_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3(lean_object* v_as_158_, size_t v_i_159_, size_t v_stop_160_, lean_object* v_b_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_eq(v_i_159_, v_stop_160_);
if (v___x_162_ == 0)
{
lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_165_; lean_object* v_snd_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_240_; 
v_fst_163_ = lean_ctor_get(v_b_161_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v_b_161_, 1);
lean_inc(v_snd_164_);
lean_dec_ref(v_b_161_);
v___x_165_ = lean_array_uget(v_as_158_, v_i_159_);
v_snd_166_ = lean_ctor_get(v___x_165_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v___x_165_, 0);
lean_dec(v_unused_241_);
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_240_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_snd_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_240_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___y_173_; lean_object* v___y_181_; lean_object* v_i_182_; lean_object* v___y_197_; lean_object* v_i_198_; lean_object* v___y_203_; lean_object* v___x_212_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_fst_163_, v___x_170_);
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(v_snd_164_, v_snd_166_);
switch(lean_obj_tag(v___x_212_))
{
case 0:
{
lean_object* v_index_213_; lean_object* v_size_214_; lean_object* v___x_215_; 
v_index_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_index_213_);
lean_dec_ref_known(v___x_212_, 3);
v_size_214_ = lean_ctor_get(v_snd_164_, 0);
lean_inc(v_size_214_);
v___x_215_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_164_, v_size_214_, v_index_213_, v_snd_166_, v_fst_163_);
lean_dec(v_index_213_);
v___y_173_ = v___x_215_;
goto v___jp_172_;
}
case 1:
{
lean_object* v_index_216_; lean_object* v_size_217_; lean_object* v_keyArray_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_index_216_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_index_216_);
lean_dec_ref_known(v___x_212_, 1);
v_size_217_ = lean_ctor_get(v_snd_164_, 0);
v_keyArray_218_ = lean_ctor_get(v_snd_164_, 1);
v___x_219_ = lean_nat_add(v_size_217_, v___x_170_);
v___x_220_ = lean_array_get_size(v_keyArray_218_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec(v___x_219_);
lean_dec(v_index_216_);
goto v___jp_186_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_222_ = lean_unsigned_to_nat(4u);
v___x_223_ = lean_nat_mul(v___x_219_, v___x_222_);
v___x_224_ = lean_unsigned_to_nat(3u);
v___x_225_ = lean_nat_mul(v___x_220_, v___x_224_);
v___x_226_ = lean_nat_dec_le(v___x_223_, v___x_225_);
lean_dec(v___x_225_);
lean_dec(v___x_223_);
if (v___x_226_ == 0)
{
lean_dec(v___x_219_);
lean_dec(v_index_216_);
goto v___jp_186_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_164_, v___x_219_, v_index_216_, v_snd_166_, v_fst_163_);
lean_dec(v_index_216_);
v___y_173_ = v___x_227_;
goto v___jp_172_;
}
}
}
default: 
{
lean_object* v_size_228_; lean_object* v_keyArray_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_size_228_ = lean_ctor_get(v_snd_164_, 0);
v_keyArray_229_ = lean_ctor_get(v_snd_164_, 1);
v___x_230_ = lean_nat_add(v_size_228_, v___x_170_);
v___x_231_ = lean_array_get_size(v_keyArray_229_);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v___x_230_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(v_snd_164_);
lean_dec(v_snd_164_);
v___y_203_ = v___x_233_;
goto v___jp_202_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_234_ = lean_unsigned_to_nat(4u);
v___x_235_ = lean_nat_mul(v___x_230_, v___x_234_);
lean_dec(v___x_230_);
v___x_236_ = lean_unsigned_to_nat(3u);
v___x_237_ = lean_nat_mul(v___x_231_, v___x_236_);
v___x_238_ = lean_nat_dec_le(v___x_235_, v___x_237_);
lean_dec(v___x_237_);
lean_dec(v___x_235_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(v_snd_164_);
lean_dec(v_snd_164_);
v___y_203_ = v___x_239_;
goto v___jp_202_;
}
else
{
v___y_203_ = v_snd_164_;
goto v___jp_202_;
}
}
}
}
v___jp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___y_173_);
lean_ctor_set(v___x_168_, 0, v___x_171_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___y_173_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
size_t v___x_176_; size_t v___x_177_; 
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_add(v_i_159_, v___x_176_);
v_i_159_ = v___x_177_;
v_b_161_ = v___x_175_;
goto _start;
}
}
v___jp_180_:
{
lean_object* v_size_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_size_183_ = lean_ctor_get(v___y_181_, 0);
v___x_184_ = lean_nat_add(v_size_183_, v___x_170_);
v___x_185_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_181_, v___x_184_, v_i_182_, v_snd_166_, v_fst_163_);
lean_dec(v_i_182_);
v___y_173_ = v___x_185_;
goto v___jp_172_;
}
v___jp_186_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(v_snd_164_);
lean_dec(v_snd_164_);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(v___x_187_, v_snd_166_);
switch(lean_obj_tag(v___x_188_))
{
case 0:
{
lean_object* v_index_189_; lean_object* v_size_190_; lean_object* v___x_191_; 
v_index_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_index_189_);
lean_dec_ref_known(v___x_188_, 3);
v_size_190_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_size_190_);
v___x_191_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_187_, v_size_190_, v_index_189_, v_snd_166_, v_fst_163_);
lean_dec(v_index_189_);
v___y_173_ = v___x_191_;
goto v___jp_172_;
}
case 1:
{
lean_object* v_index_192_; 
v_index_192_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_index_192_);
lean_dec_ref_known(v___x_188_, 1);
v___y_181_ = v___x_187_;
v_i_182_ = v_index_192_;
goto v___jp_180_;
}
default: 
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_187_, v___x_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_index_195_; 
v_index_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_index_195_);
lean_dec_ref_known(v___x_194_, 1);
v___y_181_ = v___x_187_;
v_i_182_ = v_index_195_;
goto v___jp_180_;
}
else
{
lean_dec(v_snd_166_);
lean_dec(v_fst_163_);
v___y_173_ = v___x_187_;
goto v___jp_172_;
}
}
}
}
v___jp_196_:
{
lean_object* v_size_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_size_199_ = lean_ctor_get(v___y_197_, 0);
v___x_200_ = lean_nat_add(v_size_199_, v___x_170_);
v___x_201_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_197_, v___x_200_, v_i_198_, v_snd_166_, v_fst_163_);
lean_dec(v_i_198_);
v___y_173_ = v___x_201_;
goto v___jp_172_;
}
v___jp_202_:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(v___y_203_, v_snd_166_);
switch(lean_obj_tag(v___x_204_))
{
case 0:
{
lean_object* v_index_205_; lean_object* v_size_206_; lean_object* v___x_207_; 
v_index_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_205_);
lean_dec_ref_known(v___x_204_, 3);
v_size_206_ = lean_ctor_get(v___y_203_, 0);
lean_inc(v_size_206_);
v___x_207_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_203_, v_size_206_, v_index_205_, v_snd_166_, v_fst_163_);
lean_dec(v_index_205_);
v___y_173_ = v___x_207_;
goto v___jp_172_;
}
case 1:
{
lean_object* v_index_208_; 
v_index_208_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_204_, 1);
v___y_197_ = v___y_203_;
v_i_198_ = v_index_208_;
goto v___jp_196_;
}
default: 
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_203_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_index_211_; 
v_index_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_210_, 1);
v___y_197_ = v___y_203_;
v_i_198_ = v_index_211_;
goto v___jp_196_;
}
else
{
lean_dec(v_snd_166_);
lean_dec(v_fst_163_);
v___y_173_ = v___y_203_;
goto v___jp_172_;
}
}
}
}
}
}
else
{
return v_b_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3___boxed(lean_object* v_as_242_, lean_object* v_i_243_, lean_object* v_stop_244_, lean_object* v_b_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; lean_object* v_res_248_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_244_);
lean_dec(v_stop_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3(v_as_242_, v_i_boxed_246_, v_stop_boxed_247_, v_b_245_);
lean_dec_ref(v_as_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg(lean_object* v_hi_249_, lean_object* v_pivot_250_, lean_object* v_as_251_, lean_object* v_i_252_, lean_object* v_k_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_nat_dec_lt(v_k_253_, v_hi_249_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_k_253_);
v___x_255_ = lean_array_fswap(v_as_251_, v_i_252_, v_hi_249_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_i_252_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v_fst_258_; lean_object* v_fst_259_; uint8_t v___x_260_; 
v___x_257_ = lean_array_fget_borrowed(v_as_251_, v_k_253_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
v_fst_259_ = lean_ctor_get(v_pivot_250_, 0);
v___x_260_ = lean_expr_lt(v_fst_259_, v_fst_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_k_253_, v___x_261_);
lean_dec(v_k_253_);
v_k_253_ = v___x_262_;
goto _start;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_array_fswap(v_as_251_, v_i_252_, v_k_253_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_252_, v___x_265_);
lean_dec(v_i_252_);
v___x_267_ = lean_nat_add(v_k_253_, v___x_265_);
lean_dec(v_k_253_);
v_as_251_ = v___x_264_;
v_i_252_ = v___x_266_;
v_k_253_ = v___x_267_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg___boxed(lean_object* v_hi_269_, lean_object* v_pivot_270_, lean_object* v_as_271_, lean_object* v_i_272_, lean_object* v_k_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg(v_hi_269_, v_pivot_270_, v_as_271_, v_i_272_, v_k_273_);
lean_dec_ref(v_pivot_270_);
lean_dec(v_hi_269_);
return v_res_274_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
lean_object* v_fst_277_; lean_object* v_fst_278_; uint8_t v___x_279_; 
v_fst_277_ = lean_ctor_get(v_x_275_, 0);
v_fst_278_ = lean_ctor_get(v_x_276_, 0);
v___x_279_ = lean_expr_lt(v_fst_278_, v_fst_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_280_, v_x_281_);
lean_dec_ref(v_x_281_);
lean_dec_ref(v_x_280_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object* v_n_284_, lean_object* v_as_285_, lean_object* v_lo_286_, lean_object* v_hi_287_){
_start:
{
lean_object* v___y_289_; uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_lt(v_lo_286_, v_hi_287_);
if (v___x_299_ == 0)
{
lean_dec(v_lo_286_);
return v_as_285_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_mid_302_; lean_object* v___y_304_; lean_object* v___y_310_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_300_ = lean_nat_add(v_lo_286_, v_hi_287_);
v___x_301_ = lean_unsigned_to_nat(1u);
v_mid_302_ = lean_nat_shiftr(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
v___x_315_ = lean_array_fget_borrowed(v_as_285_, v_mid_302_);
v___x_316_ = lean_array_fget_borrowed(v_as_285_, v_lo_286_);
v___x_317_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
v___y_310_ = v_as_285_;
goto v___jp_309_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_array_fswap(v_as_285_, v_lo_286_, v_mid_302_);
v___y_310_ = v___x_318_;
goto v___jp_309_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_array_fget_borrowed(v___y_304_, v_mid_302_);
v___x_306_ = lean_array_fget_borrowed(v___y_304_, v_hi_287_);
v___x_307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v_mid_302_);
v___y_289_ = v___y_304_;
goto v___jp_288_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = lean_array_fswap(v___y_304_, v_mid_302_, v_hi_287_);
lean_dec(v_mid_302_);
v___y_289_ = v___x_308_;
goto v___jp_288_;
}
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_array_fget_borrowed(v___y_310_, v_hi_287_);
v___x_312_ = lean_array_fget_borrowed(v___y_310_, v_lo_286_);
v___x_313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_304_ = v___y_310_;
goto v___jp_303_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_array_fswap(v___y_310_, v_lo_286_, v_hi_287_);
v___y_304_ = v___x_314_;
goto v___jp_303_;
}
}
}
v___jp_288_:
{
lean_object* v_pivot_290_; lean_object* v___x_291_; lean_object* v_fst_292_; lean_object* v_snd_293_; uint8_t v___x_294_; 
v_pivot_290_ = lean_array_fget(v___y_289_, v_hi_287_);
lean_inc_n(v_lo_286_, 2);
v___x_291_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg(v_hi_287_, v_pivot_290_, v___y_289_, v_lo_286_, v_lo_286_);
lean_dec(v_pivot_290_);
v_fst_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_fst_292_);
v_snd_293_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_snd_293_);
lean_dec_ref(v___x_291_);
v___x_294_ = lean_nat_dec_le(v_hi_287_, v_fst_292_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_284_, v_snd_293_, v_lo_286_, v_fst_292_);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_fst_292_, v___x_296_);
lean_dec(v_fst_292_);
v_as_285_ = v___x_295_;
v_lo_286_ = v___x_297_;
goto _start;
}
else
{
lean_dec(v_fst_292_);
lean_dec(v_lo_286_);
return v_snd_293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object* v_n_319_, lean_object* v_as_320_, lean_object* v_lo_321_, lean_object* v_hi_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_319_, v_as_320_, v_lo_321_, v_hi_322_);
lean_dec(v_hi_322_);
lean_dec(v_n_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__2(size_t v_sz_324_, size_t v_i_325_, lean_object* v_bs_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_327_ == 0)
{
return v_bs_326_;
}
else
{
lean_object* v_v_328_; lean_object* v_fst_329_; lean_object* v___x_330_; lean_object* v_bs_x27_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_v_328_ = lean_array_uget_borrowed(v_bs_326_, v_i_325_);
v_fst_329_ = lean_ctor_get(v_v_328_, 0);
lean_inc(v_fst_329_);
v___x_330_ = lean_unsigned_to_nat(0u);
v_bs_x27_331_ = lean_array_uset(v_bs_326_, v_i_325_, v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_325_, v___x_332_);
v___x_334_ = lean_array_uset(v_bs_x27_331_, v_i_325_, v_fst_329_);
v_i_325_ = v___x_333_;
v_bs_326_ = v___x_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__2___boxed(lean_object* v_sz_336_, lean_object* v_i_337_, lean_object* v_bs_338_){
_start:
{
size_t v_sz_boxed_339_; size_t v_i_boxed_340_; lean_object* v_res_341_; 
v_sz_boxed_339_ = lean_unbox_usize(v_sz_336_);
lean_dec(v_sz_336_);
v_i_boxed_340_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__2(v_sz_boxed_339_, v_i_boxed_340_, v_bs_338_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_fst_344_; lean_object* v_fst_345_; uint8_t v___x_346_; 
v_fst_344_ = lean_ctor_get(v_x_342_, 0);
v_fst_345_ = lean_ctor_get(v_x_343_, 0);
v___x_346_ = lean_expr_lt(v_fst_344_, v_fst_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0___boxed(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0(v_x_347_, v_x_348_);
lean_dec_ref(v_x_348_);
lean_dec_ref(v_x_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg(lean_object* v_hi_351_, lean_object* v_pivot_352_, lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_k_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_nat_dec_lt(v_k_355_, v_hi_351_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_k_355_);
v___x_357_ = lean_array_fswap(v_as_353_, v_i_354_, v_hi_351_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_i_354_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v_fst_360_; lean_object* v_fst_361_; uint8_t v___x_362_; 
v___x_359_ = lean_array_fget_borrowed(v_as_353_, v_k_355_);
v_fst_360_ = lean_ctor_get(v___x_359_, 0);
v_fst_361_ = lean_ctor_get(v_pivot_352_, 0);
v___x_362_ = lean_expr_lt(v_fst_360_, v_fst_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_k_355_, v___x_363_);
lean_dec(v_k_355_);
v_k_355_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_array_fswap(v_as_353_, v_i_354_, v_k_355_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_i_354_, v___x_367_);
lean_dec(v_i_354_);
v___x_369_ = lean_nat_add(v_k_355_, v___x_367_);
lean_dec(v_k_355_);
v_as_353_ = v___x_366_;
v_i_354_ = v___x_368_;
v_k_355_ = v___x_369_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg___boxed(lean_object* v_hi_371_, lean_object* v_pivot_372_, lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_k_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg(v_hi_371_, v_pivot_372_, v_as_373_, v_i_374_, v_k_375_);
lean_dec_ref(v_pivot_372_);
lean_dec(v_hi_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg(lean_object* v_n_377_, lean_object* v_as_378_, lean_object* v_lo_379_, lean_object* v_hi_380_){
_start:
{
lean_object* v___y_382_; uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_lt(v_lo_379_, v_hi_380_);
if (v___x_392_ == 0)
{
lean_dec(v_lo_379_);
return v_as_378_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_mid_395_; lean_object* v___y_397_; lean_object* v___y_403_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_393_ = lean_nat_add(v_lo_379_, v_hi_380_);
v___x_394_ = lean_unsigned_to_nat(1u);
v_mid_395_ = lean_nat_shiftr(v___x_393_, v___x_394_);
lean_dec(v___x_393_);
v___x_408_ = lean_array_fget_borrowed(v_as_378_, v_mid_395_);
v___x_409_ = lean_array_fget_borrowed(v_as_378_, v_lo_379_);
v___x_410_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
v___y_403_ = v_as_378_;
goto v___jp_402_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = lean_array_fswap(v_as_378_, v_lo_379_, v_mid_395_);
v___y_403_ = v___x_411_;
goto v___jp_402_;
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_array_fget_borrowed(v___y_397_, v_mid_395_);
v___x_399_ = lean_array_fget_borrowed(v___y_397_, v_hi_380_);
v___x_400_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v_mid_395_);
v___y_382_ = v___y_397_;
goto v___jp_381_;
}
else
{
lean_object* v___x_401_; 
v___x_401_ = lean_array_fswap(v___y_397_, v_mid_395_, v_hi_380_);
lean_dec(v_mid_395_);
v___y_382_ = v___x_401_;
goto v___jp_381_;
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_array_fget_borrowed(v___y_403_, v_hi_380_);
v___x_405_ = lean_array_fget_borrowed(v___y_403_, v_lo_379_);
v___x_406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___lam__0(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
v___y_397_ = v___y_403_;
goto v___jp_396_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_array_fswap(v___y_403_, v_lo_379_, v_hi_380_);
v___y_397_ = v___x_407_;
goto v___jp_396_;
}
}
}
v___jp_381_:
{
lean_object* v_pivot_383_; lean_object* v___x_384_; lean_object* v_fst_385_; lean_object* v_snd_386_; uint8_t v___x_387_; 
v_pivot_383_ = lean_array_fget(v___y_382_, v_hi_380_);
lean_inc_n(v_lo_379_, 2);
v___x_384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg(v_hi_380_, v_pivot_383_, v___y_382_, v_lo_379_, v_lo_379_);
lean_dec(v_pivot_383_);
v_fst_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_fst_385_);
v_snd_386_ = lean_ctor_get(v___x_384_, 1);
lean_inc(v_snd_386_);
lean_dec_ref(v___x_384_);
v___x_387_ = lean_nat_dec_le(v_hi_380_, v_fst_385_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg(v_n_377_, v_snd_386_, v_lo_379_, v_fst_385_);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_fst_385_, v___x_389_);
lean_dec(v_fst_385_);
v_as_378_ = v___x_388_;
v_lo_379_ = v___x_390_;
goto _start;
}
else
{
lean_dec(v_fst_385_);
lean_dec(v_lo_379_);
return v_snd_386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg___boxed(lean_object* v_n_412_, lean_object* v_as_413_, lean_object* v_lo_414_, lean_object* v_hi_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg(v_n_412_, v_as_413_, v_lo_414_, v_hi_415_);
lean_dec(v_hi_415_);
lean_dec(v_n_412_);
return v_res_416_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__0(void){
_start:
{
lean_object* v_cellCount_417_; lean_object* v___x_418_; 
v_cellCount_417_ = lean_unsigned_to_nat(16u);
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__1(void){
_start:
{
lean_object* v_cellCount_419_; lean_object* v___x_420_; 
v_cellCount_419_ = lean_unsigned_to_nat(16u);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_422_ = lean_obj_once(&l_Lean_sortExprs___closed__0, &l_Lean_sortExprs___closed__0_once, _init_l_Lean_sortExprs___closed__0);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set(v___x_424_, 2, v___x_421_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object* v_es_428_, uint8_t v_lt_429_){
_start:
{
lean_object* v___y_431_; lean_object* v_snd_432_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_442_; size_t v_sz_455_; size_t v___x_456_; lean_object* v_es_457_; 
v_sz_455_ = lean_array_size(v_es_428_);
v___x_456_ = ((size_t)0ULL);
v_es_457_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg(v_sz_455_, v___x_456_, v_es_428_);
if (v_lt_429_ == 0)
{
lean_object* v___x_458_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_458_ = lean_array_get_size(v_es_457_);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_nat_dec_eq(v___x_458_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___y_468_; uint8_t v___x_470_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_sub(v___x_458_, v___x_465_);
v___x_470_ = lean_nat_dec_le(v___x_463_, v___x_466_);
if (v___x_470_ == 0)
{
lean_inc(v___x_466_);
v___y_468_ = v___x_466_;
goto v___jp_467_;
}
else
{
v___y_468_ = v___x_463_;
goto v___jp_467_;
}
v___jp_467_:
{
uint8_t v___x_469_; 
v___x_469_ = lean_nat_dec_le(v___y_468_, v___x_466_);
if (v___x_469_ == 0)
{
lean_dec(v___x_466_);
lean_inc(v___y_468_);
v___y_460_ = v___y_468_;
v___y_461_ = v___y_468_;
goto v___jp_459_;
}
else
{
v___y_460_ = v___y_468_;
v___y_461_ = v___x_466_;
goto v___jp_459_;
}
}
}
else
{
v___y_442_ = v_es_457_;
goto v___jp_441_;
}
v___jp_459_:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v___x_458_, v_es_457_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
v___y_442_ = v___x_462_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_471_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_471_ = lean_array_get_size(v_es_457_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_eq(v___x_471_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___y_481_; uint8_t v___x_483_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_sub(v___x_471_, v___x_478_);
v___x_483_ = lean_nat_dec_le(v___x_476_, v___x_479_);
if (v___x_483_ == 0)
{
lean_inc(v___x_479_);
v___y_481_ = v___x_479_;
goto v___jp_480_;
}
else
{
v___y_481_ = v___x_476_;
goto v___jp_480_;
}
v___jp_480_:
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_le(v___y_481_, v___x_479_);
if (v___x_482_ == 0)
{
lean_dec(v___x_479_);
lean_inc(v___y_481_);
v___y_473_ = v___y_481_;
v___y_474_ = v___y_481_;
goto v___jp_472_;
}
else
{
v___y_473_ = v___y_481_;
v___y_474_ = v___x_479_;
goto v___jp_472_;
}
}
}
else
{
v___y_442_ = v_es_457_;
goto v___jp_441_;
}
v___jp_472_:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg(v___x_471_, v_es_457_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
v___y_442_ = v___x_475_;
goto v___jp_441_;
}
}
v___jp_430_:
{
size_t v_sz_433_; size_t v___x_434_; lean_object* v_es_435_; lean_object* v___x_436_; 
v_sz_433_ = lean_array_size(v___y_431_);
v___x_434_ = ((size_t)0ULL);
v_es_435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__2(v_sz_433_, v___x_434_, v___y_431_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_es_435_);
lean_ctor_set(v___x_436_, 1, v_snd_432_);
return v___x_436_;
}
v___jp_437_:
{
lean_object* v_snd_440_; 
v_snd_440_ = lean_ctor_get(v___y_439_, 1);
lean_inc(v_snd_440_);
lean_dec_ref(v___y_439_);
v___y_431_ = v___y_438_;
v_snd_432_ = v_snd_440_;
goto v___jp_430_;
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_445_ = lean_array_get_size(v___y_442_);
v___x_446_ = lean_nat_dec_lt(v___x_443_, v___x_445_);
if (v___x_446_ == 0)
{
v___y_431_ = v___y_442_;
v_snd_432_ = v___x_444_;
goto v___jp_430_;
}
else
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_obj_once(&l_Lean_sortExprs___closed__3, &l_Lean_sortExprs___closed__3_once, _init_l_Lean_sortExprs___closed__3);
v___x_448_ = lean_nat_dec_le(v___x_445_, v___x_445_);
if (v___x_448_ == 0)
{
if (v___x_446_ == 0)
{
v___y_431_ = v___y_442_;
v_snd_432_ = v___x_444_;
goto v___jp_430_;
}
else
{
size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = ((size_t)0ULL);
v___x_450_ = lean_usize_of_nat(v___x_445_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3(v___y_442_, v___x_449_, v___x_450_, v___x_447_);
v___y_438_ = v___y_442_;
v___y_439_ = v___x_451_;
goto v___jp_437_;
}
}
else
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((size_t)0ULL);
v___x_453_ = lean_usize_of_nat(v___x_445_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__3(v___y_442_, v___x_452_, v___x_453_, v___x_447_);
v___y_438_ = v___y_442_;
v___y_439_ = v___x_454_;
goto v___jp_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object* v_es_484_, lean_object* v_lt_485_){
_start:
{
uint8_t v_lt_boxed_486_; lean_object* v_res_487_; 
v_lt_boxed_486_ = lean_unbox(v_lt_485_);
v_res_487_ = l_Lean_sortExprs(v_es_484_, v_lt_boxed_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0(lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_query_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___redArg(v_m_489_, v_query_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0___boxed(lean_object* v_00_u03b2_492_, lean_object* v_m_493_, lean_object* v_query_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0(v_00_u03b2_492_, v_m_493_, v_query_494_);
lean_dec(v_query_494_);
lean_dec_ref(v_m_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1(lean_object* v_00_u03b2_496_, lean_object* v_m_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___redArg(v_m_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1___boxed(lean_object* v_00_u03b2_499_, lean_object* v_m_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1(v_00_u03b2_499_, v_m_500_);
lean_dec_ref(v_m_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4(lean_object* v_as_502_, size_t v_sz_503_, size_t v_i_504_, lean_object* v_bs_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___redArg(v_sz_503_, v_i_504_, v_bs_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4___boxed(lean_object* v_as_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__4(v_as_507_, v_sz_boxed_511_, v_i_boxed_512_, v_bs_510_);
lean_dec_ref(v_as_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object* v_n_514_, lean_object* v_as_515_, lean_object* v_lo_516_, lean_object* v_hi_517_, lean_object* v_w_518_, lean_object* v_hlo_519_, lean_object* v_hhi_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_514_, v_as_515_, v_lo_516_, v_hi_517_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object* v_n_522_, lean_object* v_as_523_, lean_object* v_lo_524_, lean_object* v_hi_525_, lean_object* v_w_526_, lean_object* v_hlo_527_, lean_object* v_hhi_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(v_n_522_, v_as_523_, v_lo_524_, v_hi_525_, v_w_526_, v_hlo_527_, v_hhi_528_);
lean_dec(v_hi_525_);
lean_dec(v_n_522_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6(lean_object* v_n_530_, lean_object* v_as_531_, lean_object* v_lo_532_, lean_object* v_hi_533_, lean_object* v_w_534_, lean_object* v_hlo_535_, lean_object* v_hhi_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___redArg(v_n_530_, v_as_531_, v_lo_532_, v_hi_533_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6___boxed(lean_object* v_n_538_, lean_object* v_as_539_, lean_object* v_lo_540_, lean_object* v_hi_541_, lean_object* v_w_542_, lean_object* v_hlo_543_, lean_object* v_hhi_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6(v_n_538_, v_as_539_, v_lo_540_, v_hi_541_, v_w_542_, v_hlo_543_, v_hhi_544_);
lean_dec(v_hi_541_);
lean_dec(v_n_538_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0(lean_object* v_00_u03b2_546_, lean_object* v_m_547_, lean_object* v_query_548_, lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_m_547_, v_query_548_, v_x_549_, v_x_550_, v_x_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_554_, lean_object* v_m_555_, lean_object* v_query_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_554_, v_m_555_, v_query_556_, v_x_557_, v_x_558_, v_x_559_, v_x_560_);
lean_dec(v_query_556_);
lean_dec_ref(v_m_555_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2(lean_object* v_00_u03b2_562_, lean_object* v_init_563_, lean_object* v_b_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___redArg(v_init_563_, v_b_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_566_, lean_object* v_init_567_, lean_object* v_b_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2(v_00_u03b2_566_, v_init_567_, v_b_568_);
lean_dec_ref(v_b_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7(lean_object* v_n_570_, lean_object* v_lo_571_, lean_object* v_hi_572_, lean_object* v_hhi_573_, lean_object* v_pivot_574_, lean_object* v_as_575_, lean_object* v_i_576_, lean_object* v_k_577_, lean_object* v_ilo_578_, lean_object* v_ik_579_, lean_object* v_w_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___redArg(v_hi_572_, v_pivot_574_, v_as_575_, v_i_576_, v_k_577_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7___boxed(lean_object* v_n_582_, lean_object* v_lo_583_, lean_object* v_hi_584_, lean_object* v_hhi_585_, lean_object* v_pivot_586_, lean_object* v_as_587_, lean_object* v_i_588_, lean_object* v_k_589_, lean_object* v_ilo_590_, lean_object* v_ik_591_, lean_object* v_w_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__7(v_n_582_, v_lo_583_, v_hi_584_, v_hhi_585_, v_pivot_586_, v_as_587_, v_i_588_, v_k_589_, v_ilo_590_, v_ik_591_, v_w_592_);
lean_dec_ref(v_pivot_586_);
lean_dec(v_hi_584_);
lean_dec(v_lo_583_);
lean_dec(v_n_582_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9(lean_object* v_n_594_, lean_object* v_lo_595_, lean_object* v_hi_596_, lean_object* v_hhi_597_, lean_object* v_pivot_598_, lean_object* v_as_599_, lean_object* v_i_600_, lean_object* v_k_601_, lean_object* v_ilo_602_, lean_object* v_ik_603_, lean_object* v_w_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___redArg(v_hi_596_, v_pivot_598_, v_as_599_, v_i_600_, v_k_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9___boxed(lean_object* v_n_606_, lean_object* v_lo_607_, lean_object* v_hi_608_, lean_object* v_hhi_609_, lean_object* v_pivot_610_, lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_k_613_, lean_object* v_ilo_614_, lean_object* v_ik_615_, lean_object* v_w_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__6_spec__9(v_n_606_, v_lo_607_, v_hi_608_, v_hhi_609_, v_pivot_610_, v_as_611_, v_i_612_, v_k_613_, v_ilo_614_, v_ik_615_, v_w_616_);
lean_dec_ref(v_pivot_610_);
lean_dec(v_hi_608_);
lean_dec(v_lo_607_);
lean_dec(v_n_606_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_618_, lean_object* v_b_619_, lean_object* v_acc_620_, lean_object* v_i_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___redArg(v_b_619_, v_acc_620_, v_i_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_623_, lean_object* v_b_624_, lean_object* v_acc_625_, lean_object* v_i_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_sortExprs_spec__1_spec__2_spec__3(v_00_u03b2_623_, v_b_624_, v_acc_625_, v_i_626_);
lean_dec_ref(v_b_624_);
return v_res_627_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_SortExprs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SortExprs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_SortExprs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_SortExprs(builtin);
}
#ifdef __cplusplus
}
#endif
