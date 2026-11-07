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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_nbuckets_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_153_ = lean_array_get_size(v_data_152_);
v___x_154_ = lean_unsigned_to_nat(2u);
v_nbuckets_155_ = lean_nat_mul(v___x_153_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_box(0);
v___x_158_ = lean_mk_array(v_nbuckets_155_, v___x_157_);
v___x_159_ = lean_array_propagate_mark(v_data_152_, v___x_158_);
v___x_160_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v___x_156_, v_data_152_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object* v_a_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
lean_object* v_key_164_; lean_object* v_tail_165_; uint8_t v___x_166_; 
v_key_164_ = lean_ctor_get(v_x_162_, 0);
v_tail_165_ = lean_ctor_get(v_x_162_, 2);
v___x_166_ = lean_nat_dec_eq(v_key_164_, v_a_161_);
if (v___x_166_ == 0)
{
v_x_162_ = v_tail_165_;
goto _start;
}
else
{
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object* v_a_168_, lean_object* v_x_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_168_, v_x_169_);
lean_dec(v_x_169_);
lean_dec(v_a_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(lean_object* v_m_172_, lean_object* v_a_173_, lean_object* v_b_174_){
_start:
{
lean_object* v_size_175_; lean_object* v_buckets_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_219_; 
v_size_175_ = lean_ctor_get(v_m_172_, 0);
v_buckets_176_ = lean_ctor_get(v_m_172_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_m_172_);
if (v_isSharedCheck_219_ == 0)
{
v___x_178_ = v_m_172_;
v_isShared_179_ = v_isSharedCheck_219_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_buckets_176_);
lean_inc(v_size_175_);
lean_dec(v_m_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_219_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v_fold_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v_bkt_193_; uint8_t v___x_194_; 
v___x_180_ = lean_array_get_size(v_buckets_176_);
v___x_181_ = lean_uint64_of_nat(v_a_173_);
v___x_182_ = 32ULL;
v___x_183_ = lean_uint64_shift_right(v___x_181_, v___x_182_);
v_fold_184_ = lean_uint64_xor(v___x_181_, v___x_183_);
v___x_185_ = 16ULL;
v___x_186_ = lean_uint64_shift_right(v_fold_184_, v___x_185_);
v___x_187_ = lean_uint64_xor(v_fold_184_, v___x_186_);
v___x_188_ = lean_uint64_to_usize(v___x_187_);
v___x_189_ = lean_usize_of_nat(v___x_180_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_sub(v___x_189_, v___x_190_);
v___x_192_ = lean_usize_land(v___x_188_, v___x_191_);
v_bkt_193_ = lean_array_uget_borrowed(v_buckets_176_, v___x_192_);
v___x_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_173_, v_bkt_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_size_x27_196_; lean_object* v___x_197_; lean_object* v_buckets_x27_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v_size_x27_196_ = lean_nat_add(v_size_175_, v___x_195_);
lean_dec(v_size_175_);
lean_inc(v_bkt_193_);
v___x_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_197_, 0, v_a_173_);
lean_ctor_set(v___x_197_, 1, v_b_174_);
lean_ctor_set(v___x_197_, 2, v_bkt_193_);
v_buckets_x27_198_ = lean_array_uset(v_buckets_176_, v___x_192_, v___x_197_);
v___x_199_ = lean_unsigned_to_nat(4u);
v___x_200_ = lean_nat_mul(v_size_x27_196_, v___x_199_);
v___x_201_ = lean_unsigned_to_nat(3u);
v___x_202_ = lean_nat_div(v___x_200_, v___x_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_array_get_size(v_buckets_x27_198_);
v___x_204_ = lean_nat_dec_le(v___x_202_, v___x_203_);
lean_dec(v___x_202_);
if (v___x_204_ == 0)
{
lean_object* v_val_205_; lean_object* v___x_207_; 
v_val_205_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_buckets_x27_198_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_val_205_);
lean_ctor_set(v___x_178_, 0, v_size_x27_196_);
v___x_207_ = v___x_178_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_size_x27_196_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_val_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
else
{
lean_object* v___x_210_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_buckets_x27_198_);
lean_ctor_set(v___x_178_, 0, v_size_x27_196_);
v___x_210_ = v___x_178_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_size_x27_196_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_buckets_x27_198_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v___x_212_; lean_object* v_buckets_x27_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc(v_bkt_193_);
v___x_212_ = lean_box(0);
v_buckets_x27_213_ = lean_array_uset(v_buckets_176_, v___x_192_, v___x_212_);
v___x_214_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_173_, v_b_174_, v_bkt_193_);
v___x_215_ = lean_array_uset(v_buckets_x27_213_, v___x_192_, v___x_214_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_215_);
v___x_217_ = v___x_178_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_size_175_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(lean_object* v_as_220_, size_t v_i_221_, size_t v_stop_222_, lean_object* v_b_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_eq(v_i_221_, v_stop_222_);
if (v___x_224_ == 0)
{
lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_241_; 
v_fst_225_ = lean_ctor_get(v_b_223_, 0);
lean_inc(v_fst_225_);
v_snd_226_ = lean_ctor_get(v_b_223_, 1);
lean_inc(v_snd_226_);
lean_dec_ref(v_b_223_);
v___x_227_ = lean_array_uget(v_as_220_, v_i_221_);
v_snd_228_ = lean_ctor_get(v___x_227_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v___x_227_, 0);
lean_dec(v_unused_242_);
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_241_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_241_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_fst_225_, v___x_232_);
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_snd_226_, v_snd_228_, v_fst_225_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_234_);
lean_ctor_set(v___x_230_, 0, v___x_233_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
size_t v___x_237_; size_t v___x_238_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_221_, v___x_237_);
v_i_221_ = v___x_238_;
v_b_223_ = v___x_236_;
goto _start;
}
}
}
else
{
return v_b_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2___boxed(lean_object* v_as_243_, lean_object* v_i_244_, lean_object* v_stop_245_, lean_object* v_b_246_){
_start:
{
size_t v_i_boxed_247_; size_t v_stop_boxed_248_; lean_object* v_res_249_; 
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_stop_boxed_248_ = lean_unbox_usize(v_stop_245_);
lean_dec(v_stop_245_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v_as_243_, v_i_boxed_247_, v_stop_boxed_248_, v_b_246_);
lean_dec_ref(v_as_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(size_t v_sz_250_, size_t v_i_251_, lean_object* v_bs_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = lean_usize_dec_lt(v_i_251_, v_sz_250_);
if (v___x_253_ == 0)
{
return v_bs_252_;
}
else
{
lean_object* v_v_254_; lean_object* v___x_255_; lean_object* v_bs_x27_256_; lean_object* v___x_257_; lean_object* v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; 
v_v_254_ = lean_array_uget(v_bs_252_, v_i_251_);
v___x_255_ = lean_unsigned_to_nat(0u);
v_bs_x27_256_ = lean_array_uset(v_bs_252_, v_i_251_, v___x_255_);
v___x_257_ = lean_usize_to_nat(v_i_251_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_v_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_add(v_i_251_, v___x_259_);
v___x_261_ = lean_array_uset(v_bs_x27_256_, v_i_251_, v___x_258_);
v_i_251_ = v___x_260_;
v_bs_252_ = v___x_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object* v_sz_263_, lean_object* v_i_264_, lean_object* v_bs_265_){
_start:
{
size_t v_sz_boxed_266_; size_t v_i_boxed_267_; lean_object* v_res_268_; 
v_sz_boxed_266_ = lean_unbox_usize(v_sz_263_);
lean_dec(v_sz_263_);
v_i_boxed_267_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_boxed_266_, v_i_boxed_267_, v_bs_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(lean_object* v_hi_269_, lean_object* v_pivot_270_, lean_object* v_as_271_, lean_object* v_i_272_, lean_object* v_k_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_lt(v_k_273_, v_hi_269_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_k_273_);
v___x_275_ = lean_array_fswap(v_as_271_, v_i_272_, v_hi_269_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_i_272_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v_fst_278_; lean_object* v_fst_279_; uint8_t v___x_280_; 
v___x_277_ = lean_array_fget_borrowed(v_as_271_, v_k_273_);
v_fst_278_ = lean_ctor_get(v___x_277_, 0);
v_fst_279_ = lean_ctor_get(v_pivot_270_, 0);
v___x_280_ = lean_expr_lt(v_fst_278_, v_fst_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v_k_273_, v___x_281_);
lean_dec(v_k_273_);
v_k_273_ = v___x_282_;
goto _start;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_284_ = lean_array_fswap(v_as_271_, v_i_272_, v_k_273_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_i_272_, v___x_285_);
lean_dec(v_i_272_);
v___x_287_ = lean_nat_add(v_k_273_, v___x_285_);
lean_dec(v_k_273_);
v_as_271_ = v___x_284_;
v_i_272_ = v___x_286_;
v_k_273_ = v___x_287_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg___boxed(lean_object* v_hi_289_, lean_object* v_pivot_290_, lean_object* v_as_291_, lean_object* v_i_292_, lean_object* v_k_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_289_, v_pivot_290_, v_as_291_, v_i_292_, v_k_293_);
lean_dec_ref(v_pivot_290_);
lean_dec(v_hi_289_);
return v_res_294_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_fst_297_; lean_object* v_fst_298_; uint8_t v___x_299_; 
v_fst_297_ = lean_ctor_get(v_x_295_, 0);
v_fst_298_ = lean_ctor_get(v_x_296_, 0);
v___x_299_ = lean_expr_lt(v_fst_297_, v_fst_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_300_, v_x_301_);
lean_dec_ref(v_x_301_);
lean_dec_ref(v_x_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object* v_n_304_, lean_object* v_as_305_, lean_object* v_lo_306_, lean_object* v_hi_307_){
_start:
{
lean_object* v___y_309_; uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_lt(v_lo_306_, v_hi_307_);
if (v___x_319_ == 0)
{
lean_dec(v_lo_306_);
return v_as_305_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_mid_322_; lean_object* v___y_324_; lean_object* v___y_330_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_320_ = lean_nat_add(v_lo_306_, v_hi_307_);
v___x_321_ = lean_unsigned_to_nat(1u);
v_mid_322_ = lean_nat_shiftr(v___x_320_, v___x_321_);
lean_dec(v___x_320_);
v___x_335_ = lean_array_fget_borrowed(v_as_305_, v_mid_322_);
v___x_336_ = lean_array_fget_borrowed(v_as_305_, v_lo_306_);
v___x_337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
v___y_330_ = v_as_305_;
goto v___jp_329_;
}
else
{
lean_object* v___x_338_; 
v___x_338_ = lean_array_fswap(v_as_305_, v_lo_306_, v_mid_322_);
v___y_330_ = v___x_338_;
goto v___jp_329_;
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_325_ = lean_array_fget_borrowed(v___y_324_, v_mid_322_);
v___x_326_ = lean_array_fget_borrowed(v___y_324_, v_hi_307_);
v___x_327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_dec(v_mid_322_);
v___y_309_ = v___y_324_;
goto v___jp_308_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_array_fswap(v___y_324_, v_mid_322_, v_hi_307_);
lean_dec(v_mid_322_);
v___y_309_ = v___x_328_;
goto v___jp_308_;
}
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = lean_array_fget_borrowed(v___y_330_, v_hi_307_);
v___x_332_ = lean_array_fget_borrowed(v___y_330_, v_lo_306_);
v___x_333_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
v___y_324_ = v___y_330_;
goto v___jp_323_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_fswap(v___y_330_, v_lo_306_, v_hi_307_);
v___y_324_ = v___x_334_;
goto v___jp_323_;
}
}
}
v___jp_308_:
{
lean_object* v_pivot_310_; lean_object* v___x_311_; lean_object* v_fst_312_; lean_object* v_snd_313_; uint8_t v___x_314_; 
v_pivot_310_ = lean_array_fget(v___y_309_, v_hi_307_);
lean_inc_n(v_lo_306_, 2);
v___x_311_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_307_, v_pivot_310_, v___y_309_, v_lo_306_, v_lo_306_);
lean_dec(v_pivot_310_);
v_fst_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_fst_312_);
v_snd_313_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_snd_313_);
lean_dec_ref(v___x_311_);
v___x_314_ = lean_nat_dec_le(v_hi_307_, v_fst_312_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_304_, v_snd_313_, v_lo_306_, v_fst_312_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_fst_312_, v___x_316_);
lean_dec(v_fst_312_);
v_as_305_ = v___x_315_;
v_lo_306_ = v___x_317_;
goto _start;
}
else
{
lean_dec(v_fst_312_);
lean_dec(v_lo_306_);
return v_snd_313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object* v_n_339_, lean_object* v_as_340_, lean_object* v_lo_341_, lean_object* v_hi_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_339_, v_as_340_, v_lo_341_, v_hi_342_);
lean_dec(v_hi_342_);
lean_dec(v_n_339_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__0(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_box(0);
v___x_345_ = lean_unsigned_to_nat(16u);
v___x_346_ = lean_mk_array(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_obj_once(&l_Lean_sortExprs___closed__0, &l_Lean_sortExprs___closed__0_once, _init_l_Lean_sortExprs___closed__0);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__2(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object* v_es_353_, uint8_t v_lt_354_){
_start:
{
lean_object* v___y_356_; lean_object* v_snd_357_; lean_object* v___y_363_; size_t v_sz_373_; size_t v___x_374_; lean_object* v_es_375_; 
v_sz_373_ = lean_array_size(v_es_353_);
v___x_374_ = ((size_t)0ULL);
v_es_375_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_373_, v___x_374_, v_es_353_);
if (v_lt_354_ == 0)
{
lean_object* v___x_376_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_376_ = lean_array_get_size(v_es_375_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_nat_dec_eq(v___x_376_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___y_386_; uint8_t v___x_388_; 
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_sub(v___x_376_, v___x_383_);
v___x_388_ = lean_nat_dec_le(v___x_381_, v___x_384_);
if (v___x_388_ == 0)
{
lean_inc(v___x_384_);
v___y_386_ = v___x_384_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___x_381_;
goto v___jp_385_;
}
v___jp_385_:
{
uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_le(v___y_386_, v___x_384_);
if (v___x_387_ == 0)
{
lean_dec(v___x_384_);
lean_inc(v___y_386_);
v___y_378_ = v___y_386_;
v___y_379_ = v___y_386_;
goto v___jp_377_;
}
else
{
v___y_378_ = v___y_386_;
v___y_379_ = v___x_384_;
goto v___jp_377_;
}
}
}
else
{
v___y_363_ = v_es_375_;
goto v___jp_362_;
}
v___jp_377_:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v___x_376_, v_es_375_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
v___y_363_ = v___x_380_;
goto v___jp_362_;
}
}
else
{
lean_object* v___x_389_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_389_ = lean_array_get_size(v_es_375_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_nat_dec_eq(v___x_389_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___y_399_; uint8_t v___x_401_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_sub(v___x_389_, v___x_396_);
v___x_401_ = lean_nat_dec_le(v___x_394_, v___x_397_);
if (v___x_401_ == 0)
{
lean_inc(v___x_397_);
v___y_399_ = v___x_397_;
goto v___jp_398_;
}
else
{
v___y_399_ = v___x_394_;
goto v___jp_398_;
}
v___jp_398_:
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_le(v___y_399_, v___x_397_);
if (v___x_400_ == 0)
{
lean_dec(v___x_397_);
lean_inc(v___y_399_);
v___y_391_ = v___y_399_;
v___y_392_ = v___y_399_;
goto v___jp_390_;
}
else
{
v___y_391_ = v___y_399_;
v___y_392_ = v___x_397_;
goto v___jp_390_;
}
}
}
else
{
v___y_363_ = v_es_375_;
goto v___jp_362_;
}
v___jp_390_:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v___x_389_, v_es_375_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
v___y_363_ = v___x_393_;
goto v___jp_362_;
}
}
v___jp_355_:
{
size_t v_sz_358_; size_t v___x_359_; lean_object* v_es_360_; lean_object* v___x_361_; 
v_sz_358_ = lean_array_size(v___y_356_);
v___x_359_ = ((size_t)0ULL);
v_es_360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_358_, v___x_359_, v___y_356_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_es_360_);
lean_ctor_set(v___x_361_, 1, v_snd_357_);
return v___x_361_;
}
v___jp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_366_ = lean_array_get_size(v___y_363_);
v___x_367_ = lean_nat_dec_lt(v___x_364_, v___x_366_);
if (v___x_367_ == 0)
{
v___y_356_ = v___y_363_;
v_snd_357_ = v___x_365_;
goto v___jp_355_;
}
else
{
lean_object* v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v_snd_372_; 
v___x_368_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_369_ = ((size_t)0ULL);
v___x_370_ = lean_usize_of_nat(v___x_366_);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_363_, v___x_369_, v___x_370_, v___x_368_);
v_snd_372_ = lean_ctor_get(v___x_371_, 1);
lean_inc(v_snd_372_);
lean_dec_ref(v___x_371_);
v___y_356_ = v___y_363_;
v_snd_357_ = v_snd_372_;
goto v___jp_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object* v_es_402_, lean_object* v_lt_403_){
_start:
{
uint8_t v_lt_boxed_404_; lean_object* v_res_405_; 
v_lt_boxed_404_ = lean_unbox(v_lt_403_);
v_res_405_ = l_Lean_sortExprs(v_es_402_, v_lt_boxed_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(lean_object* v_00_u03b2_406_, lean_object* v_m_407_, lean_object* v_a_408_, lean_object* v_b_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_m_407_, v_a_408_, v_b_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(lean_object* v_as_411_, size_t v_sz_412_, size_t v_i_413_, lean_object* v_bs_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_412_, v_i_413_, v_bs_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___boxed(lean_object* v_as_416_, lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_bs_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_421_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(v_as_416_, v_sz_boxed_420_, v_i_boxed_421_, v_bs_419_);
lean_dec_ref(v_as_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(lean_object* v_n_423_, lean_object* v_as_424_, lean_object* v_lo_425_, lean_object* v_hi_426_, lean_object* v_w_427_, lean_object* v_hlo_428_, lean_object* v_hhi_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_423_, v_as_424_, v_lo_425_, v_hi_426_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(lean_object* v_n_431_, lean_object* v_as_432_, lean_object* v_lo_433_, lean_object* v_hi_434_, lean_object* v_w_435_, lean_object* v_hlo_436_, lean_object* v_hhi_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(v_n_431_, v_as_432_, v_lo_433_, v_hi_434_, v_w_435_, v_hlo_436_, v_hhi_437_);
lean_dec(v_hi_434_);
lean_dec(v_n_431_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object* v_n_439_, lean_object* v_as_440_, lean_object* v_lo_441_, lean_object* v_hi_442_, lean_object* v_w_443_, lean_object* v_hlo_444_, lean_object* v_hhi_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_439_, v_as_440_, v_lo_441_, v_hi_442_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object* v_n_447_, lean_object* v_as_448_, lean_object* v_lo_449_, lean_object* v_hi_450_, lean_object* v_w_451_, lean_object* v_hlo_452_, lean_object* v_hhi_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(v_n_447_, v_as_448_, v_lo_449_, v_hi_450_, v_w_451_, v_hlo_452_, v_hhi_453_);
lean_dec(v_hi_450_);
lean_dec(v_n_447_);
return v_res_454_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_object* v_00_u03b2_455_, lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_459_, v_a_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec(v_a_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(lean_object* v_00_u03b2_464_, lean_object* v_data_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_data_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(lean_object* v_00_u03b2_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_468_, v_b_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(lean_object* v_n_472_, lean_object* v_lo_473_, lean_object* v_hi_474_, lean_object* v_hhi_475_, lean_object* v_pivot_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_k_479_, lean_object* v_ilo_480_, lean_object* v_ik_481_, lean_object* v_w_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_474_, v_pivot_476_, v_as_477_, v_i_478_, v_k_479_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___boxed(lean_object* v_n_484_, lean_object* v_lo_485_, lean_object* v_hi_486_, lean_object* v_hhi_487_, lean_object* v_pivot_488_, lean_object* v_as_489_, lean_object* v_i_490_, lean_object* v_k_491_, lean_object* v_ilo_492_, lean_object* v_ik_493_, lean_object* v_w_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(v_n_484_, v_lo_485_, v_hi_486_, v_hhi_487_, v_pivot_488_, v_as_489_, v_i_490_, v_k_491_, v_ilo_492_, v_ik_493_, v_w_494_);
lean_dec_ref(v_pivot_488_);
lean_dec(v_hi_486_);
lean_dec(v_lo_485_);
lean_dec(v_n_484_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(lean_object* v_n_496_, lean_object* v_lo_497_, lean_object* v_hi_498_, lean_object* v_hhi_499_, lean_object* v_pivot_500_, lean_object* v_as_501_, lean_object* v_i_502_, lean_object* v_k_503_, lean_object* v_ilo_504_, lean_object* v_ik_505_, lean_object* v_w_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_498_, v_pivot_500_, v_as_501_, v_i_502_, v_k_503_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___boxed(lean_object* v_n_508_, lean_object* v_lo_509_, lean_object* v_hi_510_, lean_object* v_hhi_511_, lean_object* v_pivot_512_, lean_object* v_as_513_, lean_object* v_i_514_, lean_object* v_k_515_, lean_object* v_ilo_516_, lean_object* v_ik_517_, lean_object* v_w_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(v_n_508_, v_lo_509_, v_hi_510_, v_hhi_511_, v_pivot_512_, v_as_513_, v_i_514_, v_k_515_, v_ilo_516_, v_ik_517_, v_w_518_);
lean_dec_ref(v_pivot_512_);
lean_dec(v_hi_510_);
lean_dec(v_lo_509_);
lean_dec(v_n_508_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_520_, lean_object* v_i_521_, lean_object* v_source_522_, lean_object* v_target_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v_i_521_, v_source_522_, v_target_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_x_526_, v_x_527_);
return v___x_528_;
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
