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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1_ = stack[0].m_num;
size_t v_i_2_ = stack[1].m_num;
lean_object* v_bs_3_ = stack[2].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_1_, v_i_2_, v_bs_3_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1___boxed(lean_object* v_sz_14_, lean_object* v_i_15_, lean_object* v_bs_16_){
_start:
{
size_t v_sz_boxed_17_; size_t v_i_boxed_18_; lean_object* v_res_19_; 
v_sz_boxed_17_ = lean_unbox_usize(v_sz_14_);
lean_dec(v_sz_14_);
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_boxed_17_, v_i_boxed_18_, v_bs_16_);
return v_res_19_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_fst_22_; lean_object* v_fst_23_; uint8_t v___x_24_; 
v_fst_22_ = lean_ctor_get(v_x_20_, 0);
v_fst_23_ = lean_ctor_get(v_x_21_, 0);
v___x_24_ = lean_expr_lt(v_fst_23_, v_fst_22_);
return v___x_24_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_20_ = stack[0].m_obj;
lean_object* v_x_21_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v_x_20_, v_x_21_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0___boxed(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v_x_26_, v_x_27_);
lean_dec_ref(v_x_27_);
lean_dec_ref(v_x_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(lean_object* v_hi_30_, lean_object* v_pivot_31_, lean_object* v_as_32_, lean_object* v_i_33_, lean_object* v_k_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_nat_dec_lt(v_k_34_, v_hi_30_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_k_34_);
v___x_36_ = lean_array_fswap(v_as_32_, v_i_33_, v_hi_30_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v_i_33_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v_fst_40_; uint8_t v___x_41_; 
v___x_38_ = lean_array_fget_borrowed(v_as_32_, v_k_34_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
v_fst_40_ = lean_ctor_get(v_pivot_31_, 0);
v___x_41_ = lean_expr_lt(v_fst_40_, v_fst_39_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_k_34_, v___x_42_);
lean_dec(v_k_34_);
v_k_34_ = v___x_43_;
goto _start;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_array_fswap(v_as_32_, v_i_33_, v_k_34_);
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_add(v_i_33_, v___x_46_);
lean_dec(v_i_33_);
v___x_48_ = lean_nat_add(v_k_34_, v___x_46_);
lean_dec(v_k_34_);
v_as_32_ = v___x_45_;
v_i_33_ = v___x_47_;
v_k_34_ = v___x_48_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg___boxed(lean_object* v_hi_50_, lean_object* v_pivot_51_, lean_object* v_as_52_, lean_object* v_i_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_50_, v_pivot_51_, v_as_52_, v_i_53_, v_k_54_);
lean_dec_ref(v_pivot_51_);
lean_dec(v_hi_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(lean_object* v_n_56_, lean_object* v_as_57_, lean_object* v_lo_58_, lean_object* v_hi_59_){
_start:
{
lean_object* v___y_61_; uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_lt(v_lo_58_, v_hi_59_);
if (v___x_71_ == 0)
{
lean_dec(v_lo_58_);
return v_as_57_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_mid_74_; lean_object* v___y_76_; lean_object* v___y_82_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_72_ = lean_nat_add(v_lo_58_, v_hi_59_);
v___x_73_ = lean_unsigned_to_nat(1u);
v_mid_74_ = lean_nat_shiftr(v___x_72_, v___x_73_);
lean_dec(v___x_72_);
v___x_87_ = lean_array_fget_borrowed(v_as_57_, v_mid_74_);
v___x_88_ = lean_array_fget_borrowed(v_as_57_, v_lo_58_);
v___x_89_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
v___y_82_ = v_as_57_;
goto v___jp_81_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = lean_array_fswap(v_as_57_, v_lo_58_, v_mid_74_);
v___y_82_ = v___x_90_;
goto v___jp_81_;
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_array_fget_borrowed(v___y_76_, v_mid_74_);
v___x_78_ = lean_array_fget_borrowed(v___y_76_, v_hi_59_);
v___x_79_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_dec(v_mid_74_);
v___y_61_ = v___y_76_;
goto v___jp_60_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_array_fswap(v___y_76_, v_mid_74_, v_hi_59_);
lean_dec(v_mid_74_);
v___y_61_ = v___x_80_;
goto v___jp_60_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = lean_array_fget_borrowed(v___y_82_, v_hi_59_);
v___x_84_ = lean_array_fget_borrowed(v___y_82_, v_lo_58_);
v___x_85_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
v___y_76_ = v___y_82_;
goto v___jp_75_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_array_fswap(v___y_82_, v_lo_58_, v_hi_59_);
v___y_76_ = v___x_86_;
goto v___jp_75_;
}
}
}
v___jp_60_:
{
lean_object* v_pivot_62_; lean_object* v___x_63_; lean_object* v_fst_64_; lean_object* v_snd_65_; uint8_t v___x_66_; 
v_pivot_62_ = lean_array_fget(v___y_61_, v_hi_59_);
lean_inc_n(v_lo_58_, 2);
v___x_63_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_59_, v_pivot_62_, v___y_61_, v_lo_58_, v_lo_58_);
lean_dec(v_pivot_62_);
v_fst_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_fst_64_);
v_snd_65_ = lean_ctor_get(v___x_63_, 1);
lean_inc(v_snd_65_);
lean_dec_ref(v___x_63_);
v___x_66_ = lean_nat_dec_le(v_hi_59_, v_fst_64_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_56_, v_snd_65_, v_lo_58_, v_fst_64_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_fst_64_, v___x_68_);
lean_dec(v_fst_64_);
v_as_57_ = v___x_67_;
v_lo_58_ = v___x_69_;
goto _start;
}
else
{
lean_dec(v_fst_64_);
lean_dec(v_lo_58_);
return v_snd_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object* v_n_91_, lean_object* v_as_92_, lean_object* v_lo_93_, lean_object* v_hi_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_91_, v_as_92_, v_lo_93_, v_hi_94_);
lean_dec(v_hi_94_);
lean_dec(v_n_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(lean_object* v_a_96_, lean_object* v_b_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_dec(v_b_97_);
lean_dec(v_a_96_);
return v_x_98_;
}
else
{
lean_object* v_key_99_; lean_object* v_value_100_; lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_113_; 
v_key_99_ = lean_ctor_get(v_x_98_, 0);
v_value_100_ = lean_ctor_get(v_x_98_, 1);
v_tail_101_ = lean_ctor_get(v_x_98_, 2);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_98_);
if (v_isSharedCheck_113_ == 0)
{
v___x_103_ = v_x_98_;
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_inc(v_value_100_);
lean_inc(v_key_99_);
lean_dec(v_x_98_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_eq(v_key_99_, v_a_96_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_96_, v_b_97_, v_tail_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 2, v___x_106_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_key_99_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_value_100_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v___x_111_; 
lean_dec(v_value_100_);
lean_dec(v_key_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_b_97_);
lean_ctor_set(v___x_103_, 0, v_a_96_);
v___x_111_ = v___x_103_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_96_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_b_97_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_tail_101_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
return v_x_114_;
}
else
{
lean_object* v_key_116_; lean_object* v_value_117_; lean_object* v_tail_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_141_; 
v_key_116_ = lean_ctor_get(v_x_115_, 0);
v_value_117_ = lean_ctor_get(v_x_115_, 1);
v_tail_118_ = lean_ctor_get(v_x_115_, 2);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_141_ == 0)
{
v___x_120_ = v_x_115_;
v_isShared_121_ = v_isSharedCheck_141_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_tail_118_);
lean_inc(v_value_117_);
lean_inc(v_key_116_);
lean_dec(v_x_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_141_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v_fold_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_122_ = lean_array_get_size(v_x_114_);
v___x_123_ = lean_uint64_of_nat(v_key_116_);
v___x_124_ = 32ULL;
v___x_125_ = lean_uint64_shift_right(v___x_123_, v___x_124_);
v_fold_126_ = lean_uint64_xor(v___x_123_, v___x_125_);
v___x_127_ = 16ULL;
v___x_128_ = lean_uint64_shift_right(v_fold_126_, v___x_127_);
v___x_129_ = lean_uint64_xor(v_fold_126_, v___x_128_);
v___x_130_ = lean_uint64_to_usize(v___x_129_);
v___x_131_ = lean_usize_of_nat(v___x_122_);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_sub(v___x_131_, v___x_132_);
v___x_134_ = lean_usize_land(v___x_130_, v___x_133_);
v___x_135_ = lean_array_uget_borrowed(v_x_114_, v___x_134_);
lean_inc(v___x_135_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 2, v___x_135_);
v___x_137_ = v___x_120_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_key_116_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_value_117_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v___x_135_);
v___x_137_ = v_reuseFailAlloc_140_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; 
v___x_138_ = lean_array_uset(v_x_114_, v___x_134_, v___x_137_);
v_x_114_ = v___x_138_;
v_x_115_ = v_tail_118_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(lean_object* v_i_142_, lean_object* v_source_143_, lean_object* v_target_144_){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_array_get_size(v_source_143_);
v___x_146_ = lean_nat_dec_lt(v_i_142_, v___x_145_);
if (v___x_146_ == 0)
{
lean_dec_ref(v_source_143_);
lean_dec(v_i_142_);
return v_target_144_;
}
else
{
lean_object* v_es_147_; lean_object* v___x_148_; lean_object* v_source_149_; lean_object* v_target_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_es_147_ = lean_array_fget(v_source_143_, v_i_142_);
v___x_148_ = lean_box(0);
v_source_149_ = lean_array_fset(v_source_143_, v_i_142_, v___x_148_);
v_target_150_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_target_144_, v_es_147_);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_i_142_, v___x_151_);
lean_dec(v_i_142_);
v_i_142_ = v___x_152_;
v_source_143_ = v_source_149_;
v_target_144_ = v_target_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(lean_object* v_data_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_nbuckets_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_155_ = lean_array_get_size(v_data_154_);
v___x_156_ = lean_unsigned_to_nat(2u);
v_nbuckets_157_ = lean_nat_mul(v___x_155_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_box(0);
v___x_160_ = lean_mk_array(v_nbuckets_157_, v___x_159_);
v___x_161_ = lean_array_propagate_mark(v_data_154_, v___x_160_);
v___x_162_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v___x_158_, v_data_154_, v___x_161_);
return v___x_162_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object* v_a_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
else
{
lean_object* v_key_166_; lean_object* v_tail_167_; uint8_t v___x_168_; 
v_key_166_ = lean_ctor_get(v_x_164_, 0);
v_tail_167_ = lean_ctor_get(v_x_164_, 2);
v___x_168_ = lean_nat_dec_eq(v_key_166_, v_a_163_);
if (v___x_168_ == 0)
{
v_x_164_ = v_tail_167_;
goto _start;
}
else
{
return v___x_168_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_163_ = stack[0].m_obj;
lean_object* v_x_164_ = stack[1].m_obj;
uint8_t v_res_170_;
v_res_170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_163_, v_x_164_);
stack->m_num = v_res_170_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_171_, v_x_172_);
lean_dec(v_x_172_);
lean_dec(v_a_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(lean_object* v_m_175_, lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_size_178_; lean_object* v_buckets_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_222_; 
v_size_178_ = lean_ctor_get(v_m_175_, 0);
v_buckets_179_ = lean_ctor_get(v_m_175_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_m_175_);
if (v_isSharedCheck_222_ == 0)
{
v___x_181_ = v_m_175_;
v_isShared_182_ = v_isSharedCheck_222_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_buckets_179_);
lean_inc(v_size_178_);
lean_dec(v_m_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_222_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v_fold_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v_bkt_196_; uint8_t v___x_197_; 
v___x_183_ = lean_array_get_size(v_buckets_179_);
v___x_184_ = lean_uint64_of_nat(v_a_176_);
v___x_185_ = 32ULL;
v___x_186_ = lean_uint64_shift_right(v___x_184_, v___x_185_);
v_fold_187_ = lean_uint64_xor(v___x_184_, v___x_186_);
v___x_188_ = 16ULL;
v___x_189_ = lean_uint64_shift_right(v_fold_187_, v___x_188_);
v___x_190_ = lean_uint64_xor(v_fold_187_, v___x_189_);
v___x_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = lean_usize_of_nat(v___x_183_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_sub(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_land(v___x_191_, v___x_194_);
v_bkt_196_ = lean_array_uget_borrowed(v_buckets_179_, v___x_195_);
v___x_197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_176_, v_bkt_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v_size_x27_199_; lean_object* v___x_200_; lean_object* v_buckets_x27_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v_size_x27_199_ = lean_nat_add(v_size_178_, v___x_198_);
lean_dec(v_size_178_);
lean_inc(v_bkt_196_);
v___x_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_200_, 0, v_a_176_);
lean_ctor_set(v___x_200_, 1, v_b_177_);
lean_ctor_set(v___x_200_, 2, v_bkt_196_);
v_buckets_x27_201_ = lean_array_uset(v_buckets_179_, v___x_195_, v___x_200_);
v___x_202_ = lean_unsigned_to_nat(4u);
v___x_203_ = lean_nat_mul(v_size_x27_199_, v___x_202_);
v___x_204_ = lean_unsigned_to_nat(3u);
v___x_205_ = lean_nat_div(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_array_get_size(v_buckets_x27_201_);
v___x_207_ = lean_nat_dec_le(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
if (v___x_207_ == 0)
{
lean_object* v_val_208_; lean_object* v___x_210_; 
v_val_208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_buckets_x27_201_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_val_208_);
lean_ctor_set(v___x_181_, 0, v_size_x27_199_);
v___x_210_ = v___x_181_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_size_x27_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_val_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_object* v___x_213_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_buckets_x27_201_);
lean_ctor_set(v___x_181_, 0, v_size_x27_199_);
v___x_213_ = v___x_181_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_size_x27_199_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_buckets_x27_201_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v___x_215_; lean_object* v_buckets_x27_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
lean_inc(v_bkt_196_);
v___x_215_ = lean_box(0);
v_buckets_x27_216_ = lean_array_uset(v_buckets_179_, v___x_195_, v___x_215_);
v___x_217_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_176_, v_b_177_, v_bkt_196_);
v___x_218_ = lean_array_uset(v_buckets_x27_216_, v___x_195_, v___x_217_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_218_);
v___x_220_ = v___x_181_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_size_178_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(lean_object* v_as_223_, size_t v_i_224_, size_t v_stop_225_, lean_object* v_b_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_eq(v_i_224_, v_stop_225_);
if (v___x_227_ == 0)
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; lean_object* v_snd_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_244_; 
v_fst_228_ = lean_ctor_get(v_b_226_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_b_226_, 1);
lean_inc(v_snd_229_);
lean_dec_ref(v_b_226_);
v___x_230_ = lean_array_uget(v_as_223_, v_i_224_);
v_snd_231_ = lean_ctor_get(v___x_230_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v___x_230_, 0);
lean_dec(v_unused_245_);
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_snd_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_add(v_fst_228_, v___x_235_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_snd_229_, v_snd_231_, v_fst_228_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_237_);
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
size_t v___x_240_; size_t v___x_241_; 
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_i_224_, v___x_240_);
v_i_224_ = v___x_241_;
v_b_226_ = v___x_239_;
goto _start;
}
}
}
else
{
return v_b_226_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_223_ = stack[0].m_obj;
size_t v_i_224_ = stack[1].m_num;
size_t v_stop_225_ = stack[2].m_num;
lean_object* v_b_226_ = stack[3].m_obj;
lean_object* v_res_246_;
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v_as_223_, v_i_224_, v_stop_225_, v_b_226_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2___boxed(lean_object* v_as_247_, lean_object* v_i_248_, lean_object* v_stop_249_, lean_object* v_b_250_){
_start:
{
size_t v_i_boxed_251_; size_t v_stop_boxed_252_; lean_object* v_res_253_; 
v_i_boxed_251_ = lean_unbox_usize(v_i_248_);
lean_dec(v_i_248_);
v_stop_boxed_252_ = lean_unbox_usize(v_stop_249_);
lean_dec(v_stop_249_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v_as_247_, v_i_boxed_251_, v_stop_boxed_252_, v_b_250_);
lean_dec_ref(v_as_247_);
return v_res_253_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(size_t v_sz_254_, size_t v_i_255_, lean_object* v_bs_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_lt(v_i_255_, v_sz_254_);
if (v___x_257_ == 0)
{
return v_bs_256_;
}
else
{
lean_object* v_v_258_; lean_object* v___x_259_; lean_object* v_bs_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; 
v_v_258_ = lean_array_uget(v_bs_256_, v_i_255_);
v___x_259_ = lean_unsigned_to_nat(0u);
v_bs_x27_260_ = lean_array_uset(v_bs_256_, v_i_255_, v___x_259_);
v___x_261_ = lean_usize_to_nat(v_i_255_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_v_258_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_255_, v___x_263_);
v___x_265_ = lean_array_uset(v_bs_x27_260_, v_i_255_, v___x_262_);
v_i_255_ = v___x_264_;
v_bs_256_ = v___x_265_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_254_ = stack[0].m_num;
size_t v_i_255_ = stack[1].m_num;
lean_object* v_bs_256_ = stack[2].m_obj;
lean_object* v_res_267_;
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_254_, v_i_255_, v_bs_256_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object* v_sz_268_, lean_object* v_i_269_, lean_object* v_bs_270_){
_start:
{
size_t v_sz_boxed_271_; size_t v_i_boxed_272_; lean_object* v_res_273_; 
v_sz_boxed_271_ = lean_unbox_usize(v_sz_268_);
lean_dec(v_sz_268_);
v_i_boxed_272_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_boxed_271_, v_i_boxed_272_, v_bs_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(lean_object* v_hi_274_, lean_object* v_pivot_275_, lean_object* v_as_276_, lean_object* v_i_277_, lean_object* v_k_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_lt(v_k_278_, v_hi_274_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_k_278_);
v___x_280_ = lean_array_fswap(v_as_276_, v_i_277_, v_hi_274_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_i_277_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v_fst_283_; lean_object* v_fst_284_; uint8_t v___x_285_; 
v___x_282_ = lean_array_fget_borrowed(v_as_276_, v_k_278_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
v_fst_284_ = lean_ctor_get(v_pivot_275_, 0);
v___x_285_ = lean_expr_lt(v_fst_283_, v_fst_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_k_278_, v___x_286_);
lean_dec(v_k_278_);
v_k_278_ = v___x_287_;
goto _start;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_array_fswap(v_as_276_, v_i_277_, v_k_278_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_277_, v___x_290_);
lean_dec(v_i_277_);
v___x_292_ = lean_nat_add(v_k_278_, v___x_290_);
lean_dec(v_k_278_);
v_as_276_ = v___x_289_;
v_i_277_ = v___x_291_;
v_k_278_ = v___x_292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg___boxed(lean_object* v_hi_294_, lean_object* v_pivot_295_, lean_object* v_as_296_, lean_object* v_i_297_, lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_294_, v_pivot_295_, v_as_296_, v_i_297_, v_k_298_);
lean_dec_ref(v_pivot_295_);
lean_dec(v_hi_294_);
return v_res_299_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_fst_302_; lean_object* v_fst_303_; uint8_t v___x_304_; 
v_fst_302_ = lean_ctor_get(v_x_300_, 0);
v_fst_303_ = lean_ctor_get(v_x_301_, 0);
v___x_304_ = lean_expr_lt(v_fst_302_, v_fst_303_);
return v___x_304_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_300_ = stack[0].m_obj;
lean_object* v_x_301_ = stack[1].m_obj;
uint8_t v_res_305_;
v_res_305_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_300_, v_x_301_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_306_, v_x_307_);
lean_dec_ref(v_x_307_);
lean_dec_ref(v_x_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object* v_n_310_, lean_object* v_as_311_, lean_object* v_lo_312_, lean_object* v_hi_313_){
_start:
{
lean_object* v___y_315_; uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_lt(v_lo_312_, v_hi_313_);
if (v___x_325_ == 0)
{
lean_dec(v_lo_312_);
return v_as_311_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_mid_328_; lean_object* v___y_330_; lean_object* v___y_336_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_326_ = lean_nat_add(v_lo_312_, v_hi_313_);
v___x_327_ = lean_unsigned_to_nat(1u);
v_mid_328_ = lean_nat_shiftr(v___x_326_, v___x_327_);
lean_dec(v___x_326_);
v___x_341_ = lean_array_fget_borrowed(v_as_311_, v_mid_328_);
v___x_342_ = lean_array_fget_borrowed(v_as_311_, v_lo_312_);
v___x_343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
v___y_336_ = v_as_311_;
goto v___jp_335_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_array_fswap(v_as_311_, v_lo_312_, v_mid_328_);
v___y_336_ = v___x_344_;
goto v___jp_335_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = lean_array_fget_borrowed(v___y_330_, v_mid_328_);
v___x_332_ = lean_array_fget_borrowed(v___y_330_, v_hi_313_);
v___x_333_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_dec(v_mid_328_);
v___y_315_ = v___y_330_;
goto v___jp_314_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_array_fswap(v___y_330_, v_mid_328_, v_hi_313_);
lean_dec(v_mid_328_);
v___y_315_ = v___x_334_;
goto v___jp_314_;
}
}
v___jp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = lean_array_fget_borrowed(v___y_336_, v_hi_313_);
v___x_338_ = lean_array_fget_borrowed(v___y_336_, v_lo_312_);
v___x_339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
v___y_330_ = v___y_336_;
goto v___jp_329_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_array_fswap(v___y_336_, v_lo_312_, v_hi_313_);
v___y_330_ = v___x_340_;
goto v___jp_329_;
}
}
}
v___jp_314_:
{
lean_object* v_pivot_316_; lean_object* v___x_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; uint8_t v___x_320_; 
v_pivot_316_ = lean_array_fget(v___y_315_, v_hi_313_);
lean_inc_n(v_lo_312_, 2);
v___x_317_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_313_, v_pivot_316_, v___y_315_, v_lo_312_, v_lo_312_);
lean_dec(v_pivot_316_);
v_fst_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_fst_318_);
v_snd_319_ = lean_ctor_get(v___x_317_, 1);
lean_inc(v_snd_319_);
lean_dec_ref(v___x_317_);
v___x_320_ = lean_nat_dec_le(v_hi_313_, v_fst_318_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_310_, v_snd_319_, v_lo_312_, v_fst_318_);
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_fst_318_, v___x_322_);
lean_dec(v_fst_318_);
v_as_311_ = v___x_321_;
v_lo_312_ = v___x_323_;
goto _start;
}
else
{
lean_dec(v_fst_318_);
lean_dec(v_lo_312_);
return v_snd_319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object* v_n_345_, lean_object* v_as_346_, lean_object* v_lo_347_, lean_object* v_hi_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_345_, v_as_346_, v_lo_347_, v_hi_348_);
lean_dec(v_hi_348_);
lean_dec(v_n_345_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__0(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
v___x_351_ = lean_unsigned_to_nat(16u);
v___x_352_ = lean_mk_array(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Lean_sortExprs___closed__0, &l_Lean_sortExprs___closed__0_once, _init_l_Lean_sortExprs___closed__0);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
lean_object* l_Lean_sortExprs(lean_object* v_es_359_, uint8_t v_lt_360_){
_start:
{
lean_object* v___y_362_; lean_object* v_snd_363_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_373_; size_t v_sz_386_; size_t v___x_387_; lean_object* v_es_388_; 
v_sz_386_ = lean_array_size(v_es_359_);
v___x_387_ = ((size_t)0ULL);
v_es_388_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_386_, v___x_387_, v_es_359_);
if (v_lt_360_ == 0)
{
lean_object* v___x_389_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_389_ = lean_array_get_size(v_es_388_);
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
v___y_373_ = v_es_388_;
goto v___jp_372_;
}
v___jp_390_:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v___x_389_, v_es_388_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
v___y_373_ = v___x_393_;
goto v___jp_372_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_402_ = lean_array_get_size(v_es_388_);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_nat_dec_eq(v___x_402_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___y_412_; uint8_t v___x_414_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_sub(v___x_402_, v___x_409_);
v___x_414_ = lean_nat_dec_le(v___x_407_, v___x_410_);
if (v___x_414_ == 0)
{
lean_inc(v___x_410_);
v___y_412_ = v___x_410_;
goto v___jp_411_;
}
else
{
v___y_412_ = v___x_407_;
goto v___jp_411_;
}
v___jp_411_:
{
uint8_t v___x_413_; 
v___x_413_ = lean_nat_dec_le(v___y_412_, v___x_410_);
if (v___x_413_ == 0)
{
lean_dec(v___x_410_);
lean_inc(v___y_412_);
v___y_404_ = v___y_412_;
v___y_405_ = v___y_412_;
goto v___jp_403_;
}
else
{
v___y_404_ = v___y_412_;
v___y_405_ = v___x_410_;
goto v___jp_403_;
}
}
}
else
{
v___y_373_ = v_es_388_;
goto v___jp_372_;
}
v___jp_403_:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v___x_402_, v_es_388_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
v___y_373_ = v___x_406_;
goto v___jp_372_;
}
}
v___jp_361_:
{
size_t v_sz_364_; size_t v___x_365_; lean_object* v_es_366_; lean_object* v___x_367_; 
v_sz_364_ = lean_array_size(v___y_362_);
v___x_365_ = ((size_t)0ULL);
v_es_366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_364_, v___x_365_, v___y_362_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_es_366_);
lean_ctor_set(v___x_367_, 1, v_snd_363_);
return v___x_367_;
}
v___jp_368_:
{
lean_object* v_snd_371_; 
v_snd_371_ = lean_ctor_get(v___y_370_, 1);
lean_inc(v_snd_371_);
lean_dec_ref(v___y_370_);
v___y_362_ = v___y_369_;
v_snd_363_ = v_snd_371_;
goto v___jp_361_;
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_376_ = lean_array_get_size(v___y_373_);
v___x_377_ = lean_nat_dec_lt(v___x_374_, v___x_376_);
if (v___x_377_ == 0)
{
v___y_362_ = v___y_373_;
v_snd_363_ = v___x_375_;
goto v___jp_361_;
}
else
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_379_ = lean_nat_dec_le(v___x_376_, v___x_376_);
if (v___x_379_ == 0)
{
if (v___x_377_ == 0)
{
v___y_362_ = v___y_373_;
v_snd_363_ = v___x_375_;
goto v___jp_361_;
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((size_t)0ULL);
v___x_381_ = lean_usize_of_nat(v___x_376_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_373_, v___x_380_, v___x_381_, v___x_378_);
v___y_369_ = v___y_373_;
v___y_370_ = v___x_382_;
goto v___jp_368_;
}
}
else
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_383_ = ((size_t)0ULL);
v___x_384_ = lean_usize_of_nat(v___x_376_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_373_, v___x_383_, v___x_384_, v___x_378_);
v___y_369_ = v___y_373_;
v___y_370_ = v___x_385_;
goto v___jp_368_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_sortExprs_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_359_ = stack[0].m_obj;
uint8_t v_lt_360_ = stack[1].m_num;
lean_object* v_res_415_;
v_res_415_ = l_Lean_sortExprs(v_es_359_, v_lt_360_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object* v_es_416_, lean_object* v_lt_417_){
_start:
{
uint8_t v_lt_boxed_418_; lean_object* v_res_419_; 
v_lt_boxed_418_ = lean_unbox(v_lt_417_);
v_res_419_ = l_Lean_sortExprs(v_es_416_, v_lt_boxed_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_m_421_, v_a_422_, v_b_423_);
return v___x_424_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(lean_object* v_as_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_bs_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___redArg(v_sz_426_, v_i_427_, v_bs_428_);
return v___x_429_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_425_ = stack[0].m_obj;
size_t v_sz_426_ = stack[1].m_num;
size_t v_i_427_ = stack[2].m_num;
lean_object* v_bs_428_ = stack[3].m_obj;
lean_object* v_res_430_;
v_res_430_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(v_as_425_, v_sz_426_, v_i_427_, v_bs_428_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3___boxed(lean_object* v_as_431_, lean_object* v_sz_432_, lean_object* v_i_433_, lean_object* v_bs_434_){
_start:
{
size_t v_sz_boxed_435_; size_t v_i_boxed_436_; lean_object* v_res_437_; 
v_sz_boxed_435_ = lean_unbox_usize(v_sz_432_);
lean_dec(v_sz_432_);
v_i_boxed_436_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_sortExprs_spec__3(v_as_431_, v_sz_boxed_435_, v_i_boxed_436_, v_bs_434_);
lean_dec_ref(v_as_431_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(lean_object* v_n_438_, lean_object* v_as_439_, lean_object* v_lo_440_, lean_object* v_hi_441_, lean_object* v_w_442_, lean_object* v_hlo_443_, lean_object* v_hhi_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_438_, v_as_439_, v_lo_440_, v_hi_441_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(lean_object* v_n_446_, lean_object* v_as_447_, lean_object* v_lo_448_, lean_object* v_hi_449_, lean_object* v_w_450_, lean_object* v_hlo_451_, lean_object* v_hhi_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(v_n_446_, v_as_447_, v_lo_448_, v_hi_449_, v_w_450_, v_hlo_451_, v_hhi_452_);
lean_dec(v_hi_449_);
lean_dec(v_n_446_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object* v_n_454_, lean_object* v_as_455_, lean_object* v_lo_456_, lean_object* v_hi_457_, lean_object* v_w_458_, lean_object* v_hlo_459_, lean_object* v_hhi_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_454_, v_as_455_, v_lo_456_, v_hi_457_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object* v_n_462_, lean_object* v_as_463_, lean_object* v_lo_464_, lean_object* v_hi_465_, lean_object* v_w_466_, lean_object* v_hlo_467_, lean_object* v_hhi_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(v_n_462_, v_as_463_, v_lo_464_, v_hi_465_, v_w_466_, v_hlo_467_, v_hhi_468_);
lean_dec(v_hi_465_);
lean_dec(v_n_462_);
return v_res_469_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_object* v_00_u03b2_470_, lean_object* v_a_471_, lean_object* v_x_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_471_ = stack[1].m_obj;
lean_object* v_x_472_ = stack[2].m_obj;
uint8_t v_res_474_;
v_res_474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_box(0), v_a_471_, v_x_472_);
stack->m_num = v_res_474_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_475_, lean_object* v_a_476_, lean_object* v_x_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_475_, v_a_476_, v_x_477_);
lean_dec(v_x_477_);
lean_dec(v_a_476_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(lean_object* v_00_u03b2_480_, lean_object* v_data_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_data_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_b_485_, lean_object* v_x_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_484_, v_b_485_, v_x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(lean_object* v_n_488_, lean_object* v_lo_489_, lean_object* v_hi_490_, lean_object* v_hhi_491_, lean_object* v_pivot_492_, lean_object* v_as_493_, lean_object* v_i_494_, lean_object* v_k_495_, lean_object* v_ilo_496_, lean_object* v_ik_497_, lean_object* v_w_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_490_, v_pivot_492_, v_as_493_, v_i_494_, v_k_495_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___boxed(lean_object* v_n_500_, lean_object* v_lo_501_, lean_object* v_hi_502_, lean_object* v_hhi_503_, lean_object* v_pivot_504_, lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_k_507_, lean_object* v_ilo_508_, lean_object* v_ik_509_, lean_object* v_w_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(v_n_500_, v_lo_501_, v_hi_502_, v_hhi_503_, v_pivot_504_, v_as_505_, v_i_506_, v_k_507_, v_ilo_508_, v_ik_509_, v_w_510_);
lean_dec_ref(v_pivot_504_);
lean_dec(v_hi_502_);
lean_dec(v_lo_501_);
lean_dec(v_n_500_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(lean_object* v_n_512_, lean_object* v_lo_513_, lean_object* v_hi_514_, lean_object* v_hhi_515_, lean_object* v_pivot_516_, lean_object* v_as_517_, lean_object* v_i_518_, lean_object* v_k_519_, lean_object* v_ilo_520_, lean_object* v_ik_521_, lean_object* v_w_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_514_, v_pivot_516_, v_as_517_, v_i_518_, v_k_519_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___boxed(lean_object* v_n_524_, lean_object* v_lo_525_, lean_object* v_hi_526_, lean_object* v_hhi_527_, lean_object* v_pivot_528_, lean_object* v_as_529_, lean_object* v_i_530_, lean_object* v_k_531_, lean_object* v_ilo_532_, lean_object* v_ik_533_, lean_object* v_w_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(v_n_524_, v_lo_525_, v_hi_526_, v_hhi_527_, v_pivot_528_, v_as_529_, v_i_530_, v_k_531_, v_ilo_532_, v_ik_533_, v_w_534_);
lean_dec_ref(v_pivot_528_);
lean_dec(v_hi_526_);
lean_dec(v_lo_525_);
lean_dec(v_n_524_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_536_, lean_object* v_i_537_, lean_object* v_source_538_, lean_object* v_target_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v_i_537_, v_source_538_, v_target_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_x_542_, v_x_543_);
return v___x_544_;
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
