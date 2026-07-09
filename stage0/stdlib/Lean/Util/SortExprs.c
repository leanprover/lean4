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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(size_t v_sz_249_, size_t v_i_250_, lean_object* v_bs_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_lt(v_i_250_, v_sz_249_);
if (v___x_252_ == 0)
{
return v_bs_251_;
}
else
{
lean_object* v_v_253_; lean_object* v___x_254_; lean_object* v_bs_x27_255_; lean_object* v___x_256_; lean_object* v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v_v_253_ = lean_array_uget(v_bs_251_, v_i_250_);
v___x_254_ = lean_unsigned_to_nat(0u);
v_bs_x27_255_ = lean_array_uset(v_bs_251_, v_i_250_, v___x_254_);
v___x_256_ = lean_usize_to_nat(v_i_250_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_v_253_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_add(v_i_250_, v___x_258_);
v___x_260_ = lean_array_uset(v_bs_x27_255_, v_i_250_, v___x_257_);
v_i_250_ = v___x_259_;
v_bs_251_ = v___x_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_bs_264_){
_start:
{
size_t v_sz_boxed_265_; size_t v_i_boxed_266_; lean_object* v_res_267_; 
v_sz_boxed_265_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_266_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_boxed_265_, v_i_boxed_266_, v_bs_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(lean_object* v_hi_268_, lean_object* v_pivot_269_, lean_object* v_as_270_, lean_object* v_i_271_, lean_object* v_k_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_nat_dec_lt(v_k_272_, v_hi_268_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v_k_272_);
v___x_274_ = lean_array_fswap(v_as_270_, v_i_271_, v_hi_268_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_i_271_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v_fst_277_; lean_object* v_fst_278_; uint8_t v___x_279_; 
v___x_276_ = lean_array_fget_borrowed(v_as_270_, v_k_272_);
v_fst_277_ = lean_ctor_get(v___x_276_, 0);
v_fst_278_ = lean_ctor_get(v_pivot_269_, 0);
v___x_279_ = lean_expr_lt(v_fst_277_, v_fst_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_k_272_, v___x_280_);
lean_dec(v_k_272_);
v_k_272_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = lean_array_fswap(v_as_270_, v_i_271_, v_k_272_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_271_, v___x_284_);
lean_dec(v_i_271_);
v___x_286_ = lean_nat_add(v_k_272_, v___x_284_);
lean_dec(v_k_272_);
v_as_270_ = v___x_283_;
v_i_271_ = v___x_285_;
v_k_272_ = v___x_286_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg___boxed(lean_object* v_hi_288_, lean_object* v_pivot_289_, lean_object* v_as_290_, lean_object* v_i_291_, lean_object* v_k_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_288_, v_pivot_289_, v_as_290_, v_i_291_, v_k_292_);
lean_dec_ref(v_pivot_289_);
lean_dec(v_hi_288_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_fst_296_; lean_object* v_fst_297_; uint8_t v___x_298_; 
v_fst_296_ = lean_ctor_get(v_x_294_, 0);
v_fst_297_ = lean_ctor_get(v_x_295_, 0);
v___x_298_ = lean_expr_lt(v_fst_296_, v_fst_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_299_, v_x_300_);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_x_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object* v_n_303_, lean_object* v_as_304_, lean_object* v_lo_305_, lean_object* v_hi_306_){
_start:
{
lean_object* v___y_308_; uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_lt(v_lo_305_, v_hi_306_);
if (v___x_318_ == 0)
{
lean_dec(v_lo_305_);
return v_as_304_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_mid_321_; lean_object* v___y_323_; lean_object* v___y_329_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_319_ = lean_nat_add(v_lo_305_, v_hi_306_);
v___x_320_ = lean_unsigned_to_nat(1u);
v_mid_321_ = lean_nat_shiftr(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
v___x_334_ = lean_array_fget_borrowed(v_as_304_, v_mid_321_);
v___x_335_ = lean_array_fget_borrowed(v_as_304_, v_lo_305_);
v___x_336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
v___y_329_ = v_as_304_;
goto v___jp_328_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_array_fswap(v_as_304_, v_lo_305_, v_mid_321_);
v___y_329_ = v___x_337_;
goto v___jp_328_;
}
v___jp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = lean_array_fget_borrowed(v___y_323_, v_mid_321_);
v___x_325_ = lean_array_fget_borrowed(v___y_323_, v_hi_306_);
v___x_326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec(v_mid_321_);
v___y_308_ = v___y_323_;
goto v___jp_307_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = lean_array_fswap(v___y_323_, v_mid_321_, v_hi_306_);
lean_dec(v_mid_321_);
v___y_308_ = v___x_327_;
goto v___jp_307_;
}
}
v___jp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_array_fget_borrowed(v___y_329_, v_hi_306_);
v___x_331_ = lean_array_fget_borrowed(v___y_329_, v_lo_305_);
v___x_332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
v___y_323_ = v___y_329_;
goto v___jp_322_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = lean_array_fswap(v___y_329_, v_lo_305_, v_hi_306_);
v___y_323_ = v___x_333_;
goto v___jp_322_;
}
}
}
v___jp_307_:
{
lean_object* v_pivot_309_; lean_object* v___x_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; uint8_t v___x_313_; 
v_pivot_309_ = lean_array_fget(v___y_308_, v_hi_306_);
lean_inc_n(v_lo_305_, 2);
v___x_310_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_306_, v_pivot_309_, v___y_308_, v_lo_305_, v_lo_305_);
lean_dec(v_pivot_309_);
v_fst_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_fst_311_);
v_snd_312_ = lean_ctor_get(v___x_310_, 1);
lean_inc(v_snd_312_);
lean_dec_ref(v___x_310_);
v___x_313_ = lean_nat_dec_le(v_hi_306_, v_fst_311_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_303_, v_snd_312_, v_lo_305_, v_fst_311_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_fst_311_, v___x_315_);
lean_dec(v_fst_311_);
v_as_304_ = v___x_314_;
v_lo_305_ = v___x_316_;
goto _start;
}
else
{
lean_dec(v_fst_311_);
lean_dec(v_lo_305_);
return v_snd_312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object* v_n_338_, lean_object* v_as_339_, lean_object* v_lo_340_, lean_object* v_hi_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_338_, v_as_339_, v_lo_340_, v_hi_341_);
lean_dec(v_hi_341_);
lean_dec(v_n_338_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_unsigned_to_nat(16u);
v___x_345_ = lean_mk_array(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Lean_sortExprs___closed__0, &l_Lean_sortExprs___closed__0_once, _init_l_Lean_sortExprs___closed__0);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__2(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object* v_es_352_, uint8_t v_lt_353_){
_start:
{
lean_object* v___y_355_; lean_object* v_snd_356_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_366_; size_t v_sz_379_; size_t v___x_380_; lean_object* v_es_381_; 
v_sz_379_ = lean_array_size(v_es_352_);
v___x_380_ = ((size_t)0ULL);
v_es_381_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_379_, v___x_380_, v_es_352_);
if (v_lt_353_ == 0)
{
lean_object* v___x_382_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_382_ = lean_array_get_size(v_es_381_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_nat_dec_eq(v___x_382_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___y_392_; uint8_t v___x_394_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_sub(v___x_382_, v___x_389_);
v___x_394_ = lean_nat_dec_le(v___x_387_, v___x_390_);
if (v___x_394_ == 0)
{
lean_inc(v___x_390_);
v___y_392_ = v___x_390_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___x_387_;
goto v___jp_391_;
}
v___jp_391_:
{
uint8_t v___x_393_; 
v___x_393_ = lean_nat_dec_le(v___y_392_, v___x_390_);
if (v___x_393_ == 0)
{
lean_dec(v___x_390_);
lean_inc(v___y_392_);
v___y_384_ = v___y_392_;
v___y_385_ = v___y_392_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___y_392_;
v___y_385_ = v___x_390_;
goto v___jp_383_;
}
}
}
else
{
v___y_366_ = v_es_381_;
goto v___jp_365_;
}
v___jp_383_:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v___x_382_, v_es_381_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
v___y_366_ = v___x_386_;
goto v___jp_365_;
}
}
else
{
lean_object* v___x_395_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_395_ = lean_array_get_size(v_es_381_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_nat_dec_eq(v___x_395_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___y_405_; uint8_t v___x_407_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_sub(v___x_395_, v___x_402_);
v___x_407_ = lean_nat_dec_le(v___x_400_, v___x_403_);
if (v___x_407_ == 0)
{
lean_inc(v___x_403_);
v___y_405_ = v___x_403_;
goto v___jp_404_;
}
else
{
v___y_405_ = v___x_400_;
goto v___jp_404_;
}
v___jp_404_:
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_le(v___y_405_, v___x_403_);
if (v___x_406_ == 0)
{
lean_dec(v___x_403_);
lean_inc(v___y_405_);
v___y_397_ = v___y_405_;
v___y_398_ = v___y_405_;
goto v___jp_396_;
}
else
{
v___y_397_ = v___y_405_;
v___y_398_ = v___x_403_;
goto v___jp_396_;
}
}
}
else
{
v___y_366_ = v_es_381_;
goto v___jp_365_;
}
v___jp_396_:
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v___x_395_, v_es_381_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
v___y_366_ = v___x_399_;
goto v___jp_365_;
}
}
v___jp_354_:
{
size_t v_sz_357_; size_t v___x_358_; lean_object* v_es_359_; lean_object* v___x_360_; 
v_sz_357_ = lean_array_size(v___y_355_);
v___x_358_ = ((size_t)0ULL);
v_es_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_357_, v___x_358_, v___y_355_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_es_359_);
lean_ctor_set(v___x_360_, 1, v_snd_356_);
return v___x_360_;
}
v___jp_361_:
{
lean_object* v_snd_364_; 
v_snd_364_ = lean_ctor_get(v___y_363_, 1);
lean_inc(v_snd_364_);
lean_dec_ref(v___y_363_);
v___y_355_ = v___y_362_;
v_snd_356_ = v_snd_364_;
goto v___jp_354_;
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_369_ = lean_array_get_size(v___y_366_);
v___x_370_ = lean_nat_dec_lt(v___x_367_, v___x_369_);
if (v___x_370_ == 0)
{
v___y_355_ = v___y_366_;
v_snd_356_ = v___x_368_;
goto v___jp_354_;
}
else
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_372_ = lean_nat_dec_le(v___x_369_, v___x_369_);
if (v___x_372_ == 0)
{
if (v___x_370_ == 0)
{
v___y_355_ = v___y_366_;
v_snd_356_ = v___x_368_;
goto v___jp_354_;
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((size_t)0ULL);
v___x_374_ = lean_usize_of_nat(v___x_369_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_366_, v___x_373_, v___x_374_, v___x_371_);
v___y_362_ = v___y_366_;
v___y_363_ = v___x_375_;
goto v___jp_361_;
}
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_369_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_366_, v___x_376_, v___x_377_, v___x_371_);
v___y_362_ = v___y_366_;
v___y_363_ = v___x_378_;
goto v___jp_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object* v_es_408_, lean_object* v_lt_409_){
_start:
{
uint8_t v_lt_boxed_410_; lean_object* v_res_411_; 
v_lt_boxed_410_ = lean_unbox(v_lt_409_);
v_res_411_ = l_Lean_sortExprs(v_es_408_, v_lt_boxed_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(lean_object* v_00_u03b2_412_, lean_object* v_m_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_m_413_, v_a_414_, v_b_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(lean_object* v_as_417_, size_t v_sz_418_, size_t v_i_419_, lean_object* v_bs_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_418_, v_i_419_, v_bs_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___boxed(lean_object* v_as_422_, lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_bs_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(v_as_422_, v_sz_boxed_426_, v_i_boxed_427_, v_bs_425_);
lean_dec_ref(v_as_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(lean_object* v_n_429_, lean_object* v_as_430_, lean_object* v_lo_431_, lean_object* v_hi_432_, lean_object* v_w_433_, lean_object* v_hlo_434_, lean_object* v_hhi_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_429_, v_as_430_, v_lo_431_, v_hi_432_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(lean_object* v_n_437_, lean_object* v_as_438_, lean_object* v_lo_439_, lean_object* v_hi_440_, lean_object* v_w_441_, lean_object* v_hlo_442_, lean_object* v_hhi_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(v_n_437_, v_as_438_, v_lo_439_, v_hi_440_, v_w_441_, v_hlo_442_, v_hhi_443_);
lean_dec(v_hi_440_);
lean_dec(v_n_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object* v_n_445_, lean_object* v_as_446_, lean_object* v_lo_447_, lean_object* v_hi_448_, lean_object* v_w_449_, lean_object* v_hlo_450_, lean_object* v_hhi_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_445_, v_as_446_, v_lo_447_, v_hi_448_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object* v_n_453_, lean_object* v_as_454_, lean_object* v_lo_455_, lean_object* v_hi_456_, lean_object* v_w_457_, lean_object* v_hlo_458_, lean_object* v_hhi_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(v_n_453_, v_as_454_, v_lo_455_, v_hi_456_, v_w_457_, v_hlo_458_, v_hhi_459_);
lean_dec(v_hi_456_);
lean_dec(v_n_453_);
return v_res_460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_465_, lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_465_, v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_a_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_data_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_data_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_474_, v_b_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(lean_object* v_n_478_, lean_object* v_lo_479_, lean_object* v_hi_480_, lean_object* v_hhi_481_, lean_object* v_pivot_482_, lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_k_485_, lean_object* v_ilo_486_, lean_object* v_ik_487_, lean_object* v_w_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_480_, v_pivot_482_, v_as_483_, v_i_484_, v_k_485_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___boxed(lean_object* v_n_490_, lean_object* v_lo_491_, lean_object* v_hi_492_, lean_object* v_hhi_493_, lean_object* v_pivot_494_, lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_k_497_, lean_object* v_ilo_498_, lean_object* v_ik_499_, lean_object* v_w_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(v_n_490_, v_lo_491_, v_hi_492_, v_hhi_493_, v_pivot_494_, v_as_495_, v_i_496_, v_k_497_, v_ilo_498_, v_ik_499_, v_w_500_);
lean_dec_ref(v_pivot_494_);
lean_dec(v_hi_492_);
lean_dec(v_lo_491_);
lean_dec(v_n_490_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(lean_object* v_n_502_, lean_object* v_lo_503_, lean_object* v_hi_504_, lean_object* v_hhi_505_, lean_object* v_pivot_506_, lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_k_509_, lean_object* v_ilo_510_, lean_object* v_ik_511_, lean_object* v_w_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_504_, v_pivot_506_, v_as_507_, v_i_508_, v_k_509_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___boxed(lean_object* v_n_514_, lean_object* v_lo_515_, lean_object* v_hi_516_, lean_object* v_hhi_517_, lean_object* v_pivot_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_k_521_, lean_object* v_ilo_522_, lean_object* v_ik_523_, lean_object* v_w_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(v_n_514_, v_lo_515_, v_hi_516_, v_hhi_517_, v_pivot_518_, v_as_519_, v_i_520_, v_k_521_, v_ilo_522_, v_ik_523_, v_w_524_);
lean_dec_ref(v_pivot_518_);
lean_dec(v_hi_516_);
lean_dec(v_lo_515_);
lean_dec(v_n_514_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_526_, lean_object* v_i_527_, lean_object* v_source_528_, lean_object* v_target_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v_i_527_, v_source_528_, v_target_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_x_532_, v_x_533_);
return v___x_534_;
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
