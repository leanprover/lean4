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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_sortExprs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__0;
static lean_once_cell_t l_Lean_sortExprs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__1;
static lean_once_cell_t l_Lean_sortExprs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_sortExprs___closed__2;
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
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
lean_object* v_v_5_; lean_object* v_fst_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; 
v_v_5_ = lean_array_uget_borrowed(v_bs_3_, v_i_2_);
v_fst_6_ = lean_ctor_get(v_v_5_, 0);
lean_inc(v_fst_6_);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_7_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_array_uset(v_bs_x27_8_, v_i_2_, v_fst_6_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_11_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1___boxed(lean_object* v_sz_13_, lean_object* v_i_14_, lean_object* v_bs_15_){
_start:
{
size_t v_sz_boxed_16_; size_t v_i_boxed_17_; lean_object* v_res_18_; 
v_sz_boxed_16_ = lean_unbox_usize(v_sz_13_);
lean_dec(v_sz_13_);
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_boxed_16_, v_i_boxed_17_, v_bs_15_);
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_fst_21_; lean_object* v_fst_22_; uint8_t v___x_23_; 
v_fst_21_ = lean_ctor_get(v_x_19_, 0);
v_fst_22_ = lean_ctor_get(v_x_20_, 0);
v___x_23_ = lean_expr_lt(v_fst_22_, v_fst_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v_x_24_, v_x_25_);
lean_dec_ref(v_x_25_);
lean_dec_ref(v_x_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(lean_object* v_hi_28_, lean_object* v_pivot_29_, lean_object* v_as_30_, lean_object* v_i_31_, lean_object* v_k_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = lean_nat_dec_lt(v_k_32_, v_hi_28_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_k_32_);
v___x_34_ = lean_array_fswap(v_as_30_, v_i_31_, v_hi_28_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_i_31_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v_fst_37_; lean_object* v_fst_38_; uint8_t v___x_39_; 
v___x_36_ = lean_array_fget_borrowed(v_as_30_, v_k_32_);
v_fst_37_ = lean_ctor_get(v___x_36_, 0);
v_fst_38_ = lean_ctor_get(v_pivot_29_, 0);
v___x_39_ = lean_expr_lt(v_fst_38_, v_fst_37_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_add(v_k_32_, v___x_40_);
lean_dec(v_k_32_);
v_k_32_ = v___x_41_;
goto _start;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = lean_array_fswap(v_as_30_, v_i_31_, v_k_32_);
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_i_31_, v___x_44_);
lean_dec(v_i_31_);
v___x_46_ = lean_nat_add(v_k_32_, v___x_44_);
lean_dec(v_k_32_);
v_as_30_ = v___x_43_;
v_i_31_ = v___x_45_;
v_k_32_ = v___x_46_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg___boxed(lean_object* v_hi_48_, lean_object* v_pivot_49_, lean_object* v_as_50_, lean_object* v_i_51_, lean_object* v_k_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_48_, v_pivot_49_, v_as_50_, v_i_51_, v_k_52_);
lean_dec_ref(v_pivot_49_);
lean_dec(v_hi_48_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(lean_object* v_n_54_, lean_object* v_as_55_, lean_object* v_lo_56_, lean_object* v_hi_57_){
_start:
{
lean_object* v___y_59_; uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_lt(v_lo_56_, v_hi_57_);
if (v___x_69_ == 0)
{
lean_dec(v_lo_56_);
return v_as_55_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_mid_72_; lean_object* v___y_74_; lean_object* v___y_80_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_70_ = lean_nat_add(v_lo_56_, v_hi_57_);
v___x_71_ = lean_unsigned_to_nat(1u);
v_mid_72_ = lean_nat_shiftr(v___x_70_, v___x_71_);
lean_dec(v___x_70_);
v___x_85_ = lean_array_fget_borrowed(v_as_55_, v_mid_72_);
v___x_86_ = lean_array_fget_borrowed(v_as_55_, v_lo_56_);
v___x_87_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
v___y_80_ = v_as_55_;
goto v___jp_79_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = lean_array_fswap(v_as_55_, v_lo_56_, v_mid_72_);
v___y_80_ = v___x_88_;
goto v___jp_79_;
}
v___jp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_array_fget_borrowed(v___y_74_, v_mid_72_);
v___x_76_ = lean_array_fget_borrowed(v___y_74_, v_hi_57_);
v___x_77_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec(v_mid_72_);
v___y_59_ = v___y_74_;
goto v___jp_58_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = lean_array_fswap(v___y_74_, v_mid_72_, v_hi_57_);
lean_dec(v_mid_72_);
v___y_59_ = v___x_78_;
goto v___jp_58_;
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_array_fget_borrowed(v___y_80_, v_hi_57_);
v___x_82_ = lean_array_fget_borrowed(v___y_80_, v_lo_56_);
v___x_83_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
v___y_74_ = v___y_80_;
goto v___jp_73_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = lean_array_fswap(v___y_80_, v_lo_56_, v_hi_57_);
v___y_74_ = v___x_84_;
goto v___jp_73_;
}
}
}
v___jp_58_:
{
lean_object* v_pivot_60_; lean_object* v___x_61_; lean_object* v_fst_62_; lean_object* v_snd_63_; uint8_t v___x_64_; 
v_pivot_60_ = lean_array_fget(v___y_59_, v_hi_57_);
lean_inc_n(v_lo_56_, 2);
v___x_61_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_57_, v_pivot_60_, v___y_59_, v_lo_56_, v_lo_56_);
lean_dec(v_pivot_60_);
v_fst_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_fst_62_);
v_snd_63_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_snd_63_);
lean_dec_ref(v___x_61_);
v___x_64_ = lean_nat_dec_le(v_hi_57_, v_fst_62_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_54_, v_snd_63_, v_lo_56_, v_fst_62_);
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_fst_62_, v___x_66_);
lean_dec(v_fst_62_);
v_as_55_ = v___x_65_;
v_lo_56_ = v___x_67_;
goto _start;
}
else
{
lean_dec(v_fst_62_);
lean_dec(v_lo_56_);
return v_snd_63_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object* v_n_89_, lean_object* v_as_90_, lean_object* v_lo_91_, lean_object* v_hi_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_89_, v_as_90_, v_lo_91_, v_hi_92_);
lean_dec(v_hi_92_);
lean_dec(v_n_89_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(lean_object* v_a_94_, lean_object* v_b_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_dec(v_b_95_);
lean_dec(v_a_94_);
return v_x_96_;
}
else
{
lean_object* v_key_97_; lean_object* v_value_98_; lean_object* v_tail_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_111_; 
v_key_97_ = lean_ctor_get(v_x_96_, 0);
v_value_98_ = lean_ctor_get(v_x_96_, 1);
v_tail_99_ = lean_ctor_get(v_x_96_, 2);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_111_ == 0)
{
v___x_101_ = v_x_96_;
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_tail_99_);
lean_inc(v_value_98_);
lean_inc(v_key_97_);
lean_dec(v_x_96_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_eq(v_key_97_, v_a_94_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_94_, v_b_95_, v_tail_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 2, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_key_97_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_value_98_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec(v_value_98_);
lean_dec(v_key_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_b_95_);
lean_ctor_set(v___x_101_, 0, v_a_94_);
v___x_109_ = v___x_101_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_94_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_b_95_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_tail_99_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
return v_x_112_;
}
else
{
lean_object* v_key_114_; lean_object* v_value_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_139_; 
v_key_114_ = lean_ctor_get(v_x_113_, 0);
v_value_115_ = lean_ctor_get(v_x_113_, 1);
v_tail_116_ = lean_ctor_get(v_x_113_, 2);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_139_ == 0)
{
v___x_118_ = v_x_113_;
v_isShared_119_ = v_isSharedCheck_139_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_value_115_);
lean_inc(v_key_114_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_139_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v_fold_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_120_ = lean_array_get_size(v_x_112_);
v___x_121_ = lean_uint64_of_nat(v_key_114_);
v___x_122_ = 32ULL;
v___x_123_ = lean_uint64_shift_right(v___x_121_, v___x_122_);
v_fold_124_ = lean_uint64_xor(v___x_121_, v___x_123_);
v___x_125_ = 16ULL;
v___x_126_ = lean_uint64_shift_right(v_fold_124_, v___x_125_);
v___x_127_ = lean_uint64_xor(v_fold_124_, v___x_126_);
v___x_128_ = lean_uint64_to_usize(v___x_127_);
v___x_129_ = lean_usize_of_nat(v___x_120_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v___x_129_, v___x_130_);
v___x_132_ = lean_usize_land(v___x_128_, v___x_131_);
v___x_133_ = lean_array_uget_borrowed(v_x_112_, v___x_132_);
lean_inc(v___x_133_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v___x_133_);
v___x_135_ = v___x_118_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_key_114_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_value_115_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v___x_133_);
v___x_135_ = v_reuseFailAlloc_138_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; 
v___x_136_ = lean_array_uset(v_x_112_, v___x_132_, v___x_135_);
v_x_112_ = v___x_136_;
v_x_113_ = v_tail_116_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(lean_object* v_i_140_, lean_object* v_source_141_, lean_object* v_target_142_){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_array_get_size(v_source_141_);
v___x_144_ = lean_nat_dec_lt(v_i_140_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec_ref(v_source_141_);
lean_dec(v_i_140_);
return v_target_142_;
}
else
{
lean_object* v_es_145_; lean_object* v___x_146_; lean_object* v_source_147_; lean_object* v_target_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_es_145_ = lean_array_fget(v_source_141_, v_i_140_);
v___x_146_ = lean_box(0);
v_source_147_ = lean_array_fset(v_source_141_, v_i_140_, v___x_146_);
v_target_148_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_target_142_, v_es_145_);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_add(v_i_140_, v___x_149_);
lean_dec(v_i_140_);
v_i_140_ = v___x_150_;
v_source_141_ = v_source_147_;
v_target_142_ = v_target_148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(lean_object* v_data_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_nbuckets_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_153_ = lean_array_get_size(v_data_152_);
v___x_154_ = lean_unsigned_to_nat(2u);
v_nbuckets_155_ = lean_nat_mul(v___x_153_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_box(0);
v___x_158_ = lean_mk_array(v_nbuckets_155_, v___x_157_);
v___x_159_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v___x_156_, v_data_152_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object* v_a_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
lean_object* v_key_163_; lean_object* v_tail_164_; uint8_t v___x_165_; 
v_key_163_ = lean_ctor_get(v_x_161_, 0);
v_tail_164_ = lean_ctor_get(v_x_161_, 2);
v___x_165_ = lean_nat_dec_eq(v_key_163_, v_a_160_);
if (v___x_165_ == 0)
{
v_x_161_ = v_tail_164_;
goto _start;
}
else
{
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object* v_a_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v_a_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(lean_object* v_m_171_, lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
lean_object* v_size_174_; lean_object* v_buckets_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_218_; 
v_size_174_ = lean_ctor_get(v_m_171_, 0);
v_buckets_175_ = lean_ctor_get(v_m_171_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_m_171_);
if (v_isSharedCheck_218_ == 0)
{
v___x_177_ = v_m_171_;
v_isShared_178_ = v_isSharedCheck_218_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_buckets_175_);
lean_inc(v_size_174_);
lean_dec(v_m_171_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_218_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v_fold_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v_bkt_192_; uint8_t v___x_193_; 
v___x_179_ = lean_array_get_size(v_buckets_175_);
v___x_180_ = lean_uint64_of_nat(v_a_172_);
v___x_181_ = 32ULL;
v___x_182_ = lean_uint64_shift_right(v___x_180_, v___x_181_);
v_fold_183_ = lean_uint64_xor(v___x_180_, v___x_182_);
v___x_184_ = 16ULL;
v___x_185_ = lean_uint64_shift_right(v_fold_183_, v___x_184_);
v___x_186_ = lean_uint64_xor(v_fold_183_, v___x_185_);
v___x_187_ = lean_uint64_to_usize(v___x_186_);
v___x_188_ = lean_usize_of_nat(v___x_179_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_sub(v___x_188_, v___x_189_);
v___x_191_ = lean_usize_land(v___x_187_, v___x_190_);
v_bkt_192_ = lean_array_uget_borrowed(v_buckets_175_, v___x_191_);
v___x_193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_172_, v_bkt_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v_size_x27_195_; lean_object* v___x_196_; lean_object* v_buckets_x27_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v_size_x27_195_ = lean_nat_add(v_size_174_, v___x_194_);
lean_dec(v_size_174_);
lean_inc(v_bkt_192_);
v___x_196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_196_, 0, v_a_172_);
lean_ctor_set(v___x_196_, 1, v_b_173_);
lean_ctor_set(v___x_196_, 2, v_bkt_192_);
v_buckets_x27_197_ = lean_array_uset(v_buckets_175_, v___x_191_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(4u);
v___x_199_ = lean_nat_mul(v_size_x27_195_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(3u);
v___x_201_ = lean_nat_div(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_array_get_size(v_buckets_x27_197_);
v___x_203_ = lean_nat_dec_le(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
if (v___x_203_ == 0)
{
lean_object* v_val_204_; lean_object* v___x_206_; 
v_val_204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_buckets_x27_197_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_val_204_);
lean_ctor_set(v___x_177_, 0, v_size_x27_195_);
v___x_206_ = v___x_177_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_size_x27_195_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_val_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
else
{
lean_object* v___x_209_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_buckets_x27_197_);
lean_ctor_set(v___x_177_, 0, v_size_x27_195_);
v___x_209_ = v___x_177_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_size_x27_195_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_buckets_x27_197_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v___x_211_; lean_object* v_buckets_x27_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
lean_inc(v_bkt_192_);
v___x_211_ = lean_box(0);
v_buckets_x27_212_ = lean_array_uset(v_buckets_175_, v___x_191_, v___x_211_);
v___x_213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_172_, v_b_173_, v_bkt_192_);
v___x_214_ = lean_array_uset(v_buckets_x27_212_, v___x_191_, v___x_213_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_214_);
v___x_216_ = v___x_177_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_size_174_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(lean_object* v_as_219_, size_t v_i_220_, size_t v_stop_221_, lean_object* v_b_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lean_usize_dec_eq(v_i_220_, v_stop_221_);
if (v___x_223_ == 0)
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_226_; lean_object* v_snd_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_240_; 
v_fst_224_ = lean_ctor_get(v_b_222_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v_b_222_, 1);
lean_inc(v_snd_225_);
lean_dec_ref(v_b_222_);
v___x_226_ = lean_array_uget(v_as_219_, v_i_220_);
v_snd_227_ = lean_ctor_get(v___x_226_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v___x_226_, 0);
lean_dec(v_unused_241_);
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_240_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_snd_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_240_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_fst_224_, v___x_231_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_snd_225_, v_snd_227_, v_fst_224_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_233_);
lean_ctor_set(v___x_229_, 0, v___x_232_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_239_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
size_t v___x_236_; size_t v___x_237_; 
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_i_220_, v___x_236_);
v_i_220_ = v___x_237_;
v_b_222_ = v___x_235_;
goto _start;
}
}
}
else
{
return v_b_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2___boxed(lean_object* v_as_242_, lean_object* v_i_243_, lean_object* v_stop_244_, lean_object* v_b_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; lean_object* v_res_248_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_244_);
lean_dec(v_stop_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v_as_242_, v_i_boxed_246_, v_stop_boxed_247_, v_b_245_);
lean_dec_ref(v_as_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_j_251_, lean_object* v_bs_252_){
_start:
{
lean_object* v_zero_253_; uint8_t v_isZero_254_; 
v_zero_253_ = lean_unsigned_to_nat(0u);
v_isZero_254_ = lean_nat_dec_eq(v_i_250_, v_zero_253_);
if (v_isZero_254_ == 1)
{
lean_dec(v_j_251_);
lean_dec(v_i_250_);
return v_bs_252_;
}
else
{
lean_object* v_one_255_; lean_object* v_n_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_one_255_ = lean_unsigned_to_nat(1u);
v_n_256_ = lean_nat_sub(v_i_250_, v_one_255_);
lean_dec(v_i_250_);
v___x_257_ = lean_array_fget_borrowed(v_as_249_, v_j_251_);
lean_inc(v_j_251_);
lean_inc(v___x_257_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_j_251_);
v___x_259_ = lean_nat_add(v_j_251_, v_one_255_);
lean_dec(v_j_251_);
v___x_260_ = lean_array_push(v_bs_252_, v___x_258_);
v_i_250_ = v_n_256_;
v_j_251_ = v___x_259_;
v_bs_252_ = v___x_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object* v_as_262_, lean_object* v_i_263_, lean_object* v_j_264_, lean_object* v_bs_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(v_as_262_, v_i_263_, v_j_264_, v_bs_265_);
lean_dec_ref(v_as_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(lean_object* v_hi_267_, lean_object* v_pivot_268_, lean_object* v_as_269_, lean_object* v_i_270_, lean_object* v_k_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_lt(v_k_271_, v_hi_267_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_k_271_);
v___x_273_ = lean_array_fswap(v_as_269_, v_i_270_, v_hi_267_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_i_270_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; lean_object* v_fst_276_; lean_object* v_fst_277_; uint8_t v___x_278_; 
v___x_275_ = lean_array_fget_borrowed(v_as_269_, v_k_271_);
v_fst_276_ = lean_ctor_get(v___x_275_, 0);
v_fst_277_ = lean_ctor_get(v_pivot_268_, 0);
v___x_278_ = lean_expr_lt(v_fst_276_, v_fst_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_k_271_, v___x_279_);
lean_dec(v_k_271_);
v_k_271_ = v___x_280_;
goto _start;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_array_fswap(v_as_269_, v_i_270_, v_k_271_);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_add(v_i_270_, v___x_283_);
lean_dec(v_i_270_);
v___x_285_ = lean_nat_add(v_k_271_, v___x_283_);
lean_dec(v_k_271_);
v_as_269_ = v___x_282_;
v_i_270_ = v___x_284_;
v_k_271_ = v___x_285_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg___boxed(lean_object* v_hi_287_, lean_object* v_pivot_288_, lean_object* v_as_289_, lean_object* v_i_290_, lean_object* v_k_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_287_, v_pivot_288_, v_as_289_, v_i_290_, v_k_291_);
lean_dec_ref(v_pivot_288_);
lean_dec(v_hi_287_);
return v_res_292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_fst_295_; lean_object* v_fst_296_; uint8_t v___x_297_; 
v_fst_295_ = lean_ctor_get(v_x_293_, 0);
v_fst_296_ = lean_ctor_get(v_x_294_, 0);
v___x_297_ = lean_expr_lt(v_fst_295_, v_fst_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_298_, v_x_299_);
lean_dec_ref(v_x_299_);
lean_dec_ref(v_x_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object* v_n_302_, lean_object* v_as_303_, lean_object* v_lo_304_, lean_object* v_hi_305_){
_start:
{
lean_object* v___y_307_; uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_lt(v_lo_304_, v_hi_305_);
if (v___x_317_ == 0)
{
lean_dec(v_lo_304_);
return v_as_303_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_mid_320_; lean_object* v___y_322_; lean_object* v___y_328_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_318_ = lean_nat_add(v_lo_304_, v_hi_305_);
v___x_319_ = lean_unsigned_to_nat(1u);
v_mid_320_ = lean_nat_shiftr(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
v___x_333_ = lean_array_fget_borrowed(v_as_303_, v_mid_320_);
v___x_334_ = lean_array_fget_borrowed(v_as_303_, v_lo_304_);
v___x_335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
v___y_328_ = v_as_303_;
goto v___jp_327_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_array_fswap(v_as_303_, v_lo_304_, v_mid_320_);
v___y_328_ = v___x_336_;
goto v___jp_327_;
}
v___jp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_array_fget_borrowed(v___y_322_, v_mid_320_);
v___x_324_ = lean_array_fget_borrowed(v___y_322_, v_hi_305_);
v___x_325_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v_mid_320_);
v___y_307_ = v___y_322_;
goto v___jp_306_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_array_fswap(v___y_322_, v_mid_320_, v_hi_305_);
lean_dec(v_mid_320_);
v___y_307_ = v___x_326_;
goto v___jp_306_;
}
}
v___jp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_array_fget_borrowed(v___y_328_, v_hi_305_);
v___x_330_ = lean_array_fget_borrowed(v___y_328_, v_lo_304_);
v___x_331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
v___y_322_ = v___y_328_;
goto v___jp_321_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_array_fswap(v___y_328_, v_lo_304_, v_hi_305_);
v___y_322_ = v___x_332_;
goto v___jp_321_;
}
}
}
v___jp_306_:
{
lean_object* v_pivot_308_; lean_object* v___x_309_; lean_object* v_fst_310_; lean_object* v_snd_311_; uint8_t v___x_312_; 
v_pivot_308_ = lean_array_fget(v___y_307_, v_hi_305_);
lean_inc_n(v_lo_304_, 2);
v___x_309_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_305_, v_pivot_308_, v___y_307_, v_lo_304_, v_lo_304_);
lean_dec(v_pivot_308_);
v_fst_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_fst_310_);
v_snd_311_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_311_);
lean_dec_ref(v___x_309_);
v___x_312_ = lean_nat_dec_le(v_hi_305_, v_fst_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_302_, v_snd_311_, v_lo_304_, v_fst_310_);
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_fst_310_, v___x_314_);
lean_dec(v_fst_310_);
v_as_303_ = v___x_313_;
v_lo_304_ = v___x_315_;
goto _start;
}
else
{
lean_dec(v_fst_310_);
lean_dec(v_lo_304_);
return v_snd_311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object* v_n_337_, lean_object* v_as_338_, lean_object* v_lo_339_, lean_object* v_hi_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_337_, v_as_338_, v_lo_339_, v_hi_340_);
lean_dec(v_hi_340_);
lean_dec(v_n_337_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__0(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_box(0);
v___x_343_ = lean_unsigned_to_nat(16u);
v___x_344_ = lean_mk_array(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_sortExprs___closed__0, &l_Lean_sortExprs___closed__0_once, _init_l_Lean_sortExprs___closed__0);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__2(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object* v_es_351_, uint8_t v_lt_352_){
_start:
{
lean_object* v___y_354_; lean_object* v_snd_355_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_365_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_es_381_; 
v___x_378_ = lean_array_get_size(v_es_351_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_mk_empty_array_with_capacity(v___x_378_);
v_es_381_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(v_es_351_, v___x_378_, v___x_379_, v___x_380_);
if (v_lt_352_ == 0)
{
lean_object* v___x_382_; lean_object* v___y_384_; lean_object* v___y_385_; uint8_t v___x_387_; 
v___x_382_ = lean_array_get_size(v_es_381_);
v___x_387_ = lean_nat_dec_eq(v___x_382_, v___x_379_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___y_391_; uint8_t v___x_393_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_sub(v___x_382_, v___x_388_);
v___x_393_ = lean_nat_dec_le(v___x_379_, v___x_389_);
if (v___x_393_ == 0)
{
lean_inc(v___x_389_);
v___y_391_ = v___x_389_;
goto v___jp_390_;
}
else
{
v___y_391_ = v___x_379_;
goto v___jp_390_;
}
v___jp_390_:
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_le(v___y_391_, v___x_389_);
if (v___x_392_ == 0)
{
lean_dec(v___x_389_);
lean_inc(v___y_391_);
v___y_384_ = v___y_391_;
v___y_385_ = v___y_391_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___y_391_;
v___y_385_ = v___x_389_;
goto v___jp_383_;
}
}
}
else
{
v___y_365_ = v_es_381_;
goto v___jp_364_;
}
v___jp_383_:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v___x_382_, v_es_381_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
v___y_365_ = v___x_386_;
goto v___jp_364_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___x_399_; 
v___x_394_ = lean_array_get_size(v_es_381_);
v___x_399_ = lean_nat_dec_eq(v___x_394_, v___x_379_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___y_403_; uint8_t v___x_405_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_sub(v___x_394_, v___x_400_);
v___x_405_ = lean_nat_dec_le(v___x_379_, v___x_401_);
if (v___x_405_ == 0)
{
lean_inc(v___x_401_);
v___y_403_ = v___x_401_;
goto v___jp_402_;
}
else
{
v___y_403_ = v___x_379_;
goto v___jp_402_;
}
v___jp_402_:
{
uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_le(v___y_403_, v___x_401_);
if (v___x_404_ == 0)
{
lean_dec(v___x_401_);
lean_inc(v___y_403_);
v___y_396_ = v___y_403_;
v___y_397_ = v___y_403_;
goto v___jp_395_;
}
else
{
v___y_396_ = v___y_403_;
v___y_397_ = v___x_401_;
goto v___jp_395_;
}
}
}
else
{
v___y_365_ = v_es_381_;
goto v___jp_364_;
}
v___jp_395_:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v___x_394_, v_es_381_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
v___y_365_ = v___x_398_;
goto v___jp_364_;
}
}
v___jp_353_:
{
size_t v_sz_356_; size_t v___x_357_; lean_object* v_es_358_; lean_object* v___x_359_; 
v_sz_356_ = lean_array_size(v___y_354_);
v___x_357_ = ((size_t)0ULL);
v_es_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_356_, v___x_357_, v___y_354_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_es_358_);
lean_ctor_set(v___x_359_, 1, v_snd_355_);
return v___x_359_;
}
v___jp_360_:
{
lean_object* v_snd_363_; 
v_snd_363_ = lean_ctor_get(v___y_362_, 1);
lean_inc(v_snd_363_);
lean_dec_ref(v___y_362_);
v___y_354_ = v___y_361_;
v_snd_355_ = v_snd_363_;
goto v___jp_353_;
}
v___jp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_368_ = lean_array_get_size(v___y_365_);
v___x_369_ = lean_nat_dec_lt(v___x_366_, v___x_368_);
if (v___x_369_ == 0)
{
v___y_354_ = v___y_365_;
v_snd_355_ = v___x_367_;
goto v___jp_353_;
}
else
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_371_ = lean_nat_dec_le(v___x_368_, v___x_368_);
if (v___x_371_ == 0)
{
if (v___x_369_ == 0)
{
v___y_354_ = v___y_365_;
v_snd_355_ = v___x_367_;
goto v___jp_353_;
}
else
{
size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((size_t)0ULL);
v___x_373_ = lean_usize_of_nat(v___x_368_);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_365_, v___x_372_, v___x_373_, v___x_370_);
v___y_361_ = v___y_365_;
v___y_362_ = v___x_374_;
goto v___jp_360_;
}
}
else
{
size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((size_t)0ULL);
v___x_376_ = lean_usize_of_nat(v___x_368_);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_365_, v___x_375_, v___x_376_, v___x_370_);
v___y_361_ = v___y_365_;
v___y_362_ = v___x_377_;
goto v___jp_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object* v_es_406_, lean_object* v_lt_407_){
_start:
{
uint8_t v_lt_boxed_408_; lean_object* v_res_409_; 
v_lt_boxed_408_ = lean_unbox(v_lt_407_);
v_res_409_ = l_Lean_sortExprs(v_es_406_, v_lt_boxed_408_);
lean_dec_ref(v_es_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(lean_object* v_00_u03b2_410_, lean_object* v_m_411_, lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_m_411_, v_a_412_, v_b_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(lean_object* v_as_415_, lean_object* v_i_416_, lean_object* v_j_417_, lean_object* v_inv_418_, lean_object* v_bs_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(v_as_415_, v_i_416_, v_j_417_, v_bs_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___boxed(lean_object* v_as_421_, lean_object* v_i_422_, lean_object* v_j_423_, lean_object* v_inv_424_, lean_object* v_bs_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(v_as_421_, v_i_422_, v_j_423_, v_inv_424_, v_bs_425_);
lean_dec_ref(v_as_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(lean_object* v_n_427_, lean_object* v_as_428_, lean_object* v_lo_429_, lean_object* v_hi_430_, lean_object* v_w_431_, lean_object* v_hlo_432_, lean_object* v_hhi_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_427_, v_as_428_, v_lo_429_, v_hi_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(lean_object* v_n_435_, lean_object* v_as_436_, lean_object* v_lo_437_, lean_object* v_hi_438_, lean_object* v_w_439_, lean_object* v_hlo_440_, lean_object* v_hhi_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(v_n_435_, v_as_436_, v_lo_437_, v_hi_438_, v_w_439_, v_hlo_440_, v_hhi_441_);
lean_dec(v_hi_438_);
lean_dec(v_n_435_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object* v_n_443_, lean_object* v_as_444_, lean_object* v_lo_445_, lean_object* v_hi_446_, lean_object* v_w_447_, lean_object* v_hlo_448_, lean_object* v_hhi_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_443_, v_as_444_, v_lo_445_, v_hi_446_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object* v_n_451_, lean_object* v_as_452_, lean_object* v_lo_453_, lean_object* v_hi_454_, lean_object* v_w_455_, lean_object* v_hlo_456_, lean_object* v_hhi_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(v_n_451_, v_as_452_, v_lo_453_, v_hi_454_, v_w_455_, v_hlo_456_, v_hhi_457_);
lean_dec(v_hi_454_);
lean_dec(v_n_451_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_463_, lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_463_, v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec(v_a_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(lean_object* v_00_u03b2_468_, lean_object* v_data_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_data_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(lean_object* v_00_u03b2_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_472_, v_b_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(lean_object* v_n_476_, lean_object* v_lo_477_, lean_object* v_hi_478_, lean_object* v_hhi_479_, lean_object* v_pivot_480_, lean_object* v_as_481_, lean_object* v_i_482_, lean_object* v_k_483_, lean_object* v_ilo_484_, lean_object* v_ik_485_, lean_object* v_w_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_478_, v_pivot_480_, v_as_481_, v_i_482_, v_k_483_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___boxed(lean_object* v_n_488_, lean_object* v_lo_489_, lean_object* v_hi_490_, lean_object* v_hhi_491_, lean_object* v_pivot_492_, lean_object* v_as_493_, lean_object* v_i_494_, lean_object* v_k_495_, lean_object* v_ilo_496_, lean_object* v_ik_497_, lean_object* v_w_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(v_n_488_, v_lo_489_, v_hi_490_, v_hhi_491_, v_pivot_492_, v_as_493_, v_i_494_, v_k_495_, v_ilo_496_, v_ik_497_, v_w_498_);
lean_dec_ref(v_pivot_492_);
lean_dec(v_hi_490_);
lean_dec(v_lo_489_);
lean_dec(v_n_488_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(lean_object* v_n_500_, lean_object* v_lo_501_, lean_object* v_hi_502_, lean_object* v_hhi_503_, lean_object* v_pivot_504_, lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_k_507_, lean_object* v_ilo_508_, lean_object* v_ik_509_, lean_object* v_w_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_502_, v_pivot_504_, v_as_505_, v_i_506_, v_k_507_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___boxed(lean_object* v_n_512_, lean_object* v_lo_513_, lean_object* v_hi_514_, lean_object* v_hhi_515_, lean_object* v_pivot_516_, lean_object* v_as_517_, lean_object* v_i_518_, lean_object* v_k_519_, lean_object* v_ilo_520_, lean_object* v_ik_521_, lean_object* v_w_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(v_n_512_, v_lo_513_, v_hi_514_, v_hhi_515_, v_pivot_516_, v_as_517_, v_i_518_, v_k_519_, v_ilo_520_, v_ik_521_, v_w_522_);
lean_dec_ref(v_pivot_516_);
lean_dec(v_hi_514_);
lean_dec(v_lo_513_);
lean_dec(v_n_512_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_524_, lean_object* v_i_525_, lean_object* v_source_526_, lean_object* v_target_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v_i_525_, v_source_526_, v_target_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_x_530_, v_x_531_);
return v___x_532_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
