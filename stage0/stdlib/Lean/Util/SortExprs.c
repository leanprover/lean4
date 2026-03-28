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
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(lean_object* v_as_29_, lean_object* v_lo_30_, lean_object* v_hi_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = lean_nat_dec_lt(v_lo_30_, v_hi_31_);
if (v___x_32_ == 0)
{
lean_dec(v_lo_30_);
return v_as_29_;
}
else
{
lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v_fst_35_; lean_object* v_snd_36_; uint8_t v___x_37_; 
v___f_33_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___closed__0));
lean_inc(v_lo_30_);
v___x_34_ = l_Array_qpartition___redArg(v_as_29_, v___f_33_, v_lo_30_, v_hi_31_);
v_fst_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_fst_35_);
v_snd_36_ = lean_ctor_get(v___x_34_, 1);
lean_inc(v_snd_36_);
lean_dec_ref(v___x_34_);
v___x_37_ = lean_nat_dec_le(v_hi_31_, v_fst_35_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_snd_36_, v_lo_30_, v_fst_35_);
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_add(v_fst_35_, v___x_39_);
lean_dec(v_fst_35_);
v_as_29_ = v___x_38_;
v_lo_30_ = v___x_40_;
goto _start;
}
else
{
lean_dec(v_fst_35_);
lean_dec(v_lo_30_);
return v_snd_36_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___boxed(lean_object* v_as_42_, lean_object* v_lo_43_, lean_object* v_hi_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_as_42_, v_lo_43_, v_hi_44_);
lean_dec(v_hi_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(lean_object* v_a_46_, lean_object* v_b_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_dec(v_b_47_);
lean_dec(v_a_46_);
return v_x_48_;
}
else
{
lean_object* v_key_49_; lean_object* v_value_50_; lean_object* v_tail_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_63_; 
v_key_49_ = lean_ctor_get(v_x_48_, 0);
v_value_50_ = lean_ctor_get(v_x_48_, 1);
v_tail_51_ = lean_ctor_get(v_x_48_, 2);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_48_);
if (v_isSharedCheck_63_ == 0)
{
v___x_53_ = v_x_48_;
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_tail_51_);
lean_inc(v_value_50_);
lean_inc(v_key_49_);
lean_dec(v_x_48_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_63_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
uint8_t v___x_55_; 
v___x_55_ = lean_nat_dec_eq(v_key_49_, v_a_46_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_46_, v_b_47_, v_tail_51_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 2, v___x_56_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_key_49_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_value_50_);
lean_ctor_set(v_reuseFailAlloc_59_, 2, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
lean_object* v___x_61_; 
lean_dec(v_value_50_);
lean_dec(v_key_49_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v_b_47_);
lean_ctor_set(v___x_53_, 0, v_a_46_);
v___x_61_ = v___x_53_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_46_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_b_47_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v_tail_51_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
return v_x_64_;
}
else
{
lean_object* v_key_66_; lean_object* v_value_67_; lean_object* v_tail_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_91_; 
v_key_66_ = lean_ctor_get(v_x_65_, 0);
v_value_67_ = lean_ctor_get(v_x_65_, 1);
v_tail_68_ = lean_ctor_get(v_x_65_, 2);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_91_ == 0)
{
v___x_70_ = v_x_65_;
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_tail_68_);
lean_inc(v_value_67_);
lean_inc(v_key_66_);
lean_dec(v_x_65_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_91_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v_fold_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_72_ = lean_array_get_size(v_x_64_);
v___x_73_ = lean_uint64_of_nat(v_key_66_);
v___x_74_ = 32ULL;
v___x_75_ = lean_uint64_shift_right(v___x_73_, v___x_74_);
v_fold_76_ = lean_uint64_xor(v___x_73_, v___x_75_);
v___x_77_ = 16ULL;
v___x_78_ = lean_uint64_shift_right(v_fold_76_, v___x_77_);
v___x_79_ = lean_uint64_xor(v_fold_76_, v___x_78_);
v___x_80_ = lean_uint64_to_usize(v___x_79_);
v___x_81_ = lean_usize_of_nat(v___x_72_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_sub(v___x_81_, v___x_82_);
v___x_84_ = lean_usize_land(v___x_80_, v___x_83_);
v___x_85_ = lean_array_uget_borrowed(v_x_64_, v___x_84_);
lean_inc(v___x_85_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 2, v___x_85_);
v___x_87_ = v___x_70_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_key_66_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_value_67_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v___x_85_);
v___x_87_ = v_reuseFailAlloc_90_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; 
v___x_88_ = lean_array_uset(v_x_64_, v___x_84_, v___x_87_);
v_x_64_ = v___x_88_;
v_x_65_ = v_tail_68_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(lean_object* v_i_92_, lean_object* v_source_93_, lean_object* v_target_94_){
_start:
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_array_get_size(v_source_93_);
v___x_96_ = lean_nat_dec_lt(v_i_92_, v___x_95_);
if (v___x_96_ == 0)
{
lean_dec_ref(v_source_93_);
lean_dec(v_i_92_);
return v_target_94_;
}
else
{
lean_object* v_es_97_; lean_object* v___x_98_; lean_object* v_source_99_; lean_object* v_target_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_es_97_ = lean_array_fget(v_source_93_, v_i_92_);
v___x_98_ = lean_box(0);
v_source_99_ = lean_array_fset(v_source_93_, v_i_92_, v___x_98_);
v_target_100_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_target_94_, v_es_97_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_i_92_, v___x_101_);
lean_dec(v_i_92_);
v_i_92_ = v___x_102_;
v_source_93_ = v_source_99_;
v_target_94_ = v_target_100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(lean_object* v_data_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_nbuckets_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_105_ = lean_array_get_size(v_data_104_);
v___x_106_ = lean_unsigned_to_nat(2u);
v_nbuckets_107_ = lean_nat_mul(v___x_105_, v___x_106_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_box(0);
v___x_110_ = lean_mk_array(v_nbuckets_107_, v___x_109_);
v___x_111_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v___x_108_, v_data_104_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(lean_object* v_a_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
else
{
lean_object* v_key_115_; lean_object* v_tail_116_; uint8_t v___x_117_; 
v_key_115_ = lean_ctor_get(v_x_113_, 0);
v_tail_116_ = lean_ctor_get(v_x_113_, 2);
v___x_117_ = lean_nat_dec_eq(v_key_115_, v_a_112_);
if (v___x_117_ == 0)
{
v_x_113_ = v_tail_116_;
goto _start;
}
else
{
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(lean_object* v_a_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_119_, v_x_120_);
lean_dec(v_x_120_);
lean_dec(v_a_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(lean_object* v_m_123_, lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
lean_object* v_size_126_; lean_object* v_buckets_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_170_; 
v_size_126_ = lean_ctor_get(v_m_123_, 0);
v_buckets_127_ = lean_ctor_get(v_m_123_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_m_123_);
if (v_isSharedCheck_170_ == 0)
{
v___x_129_ = v_m_123_;
v_isShared_130_ = v_isSharedCheck_170_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_buckets_127_);
lean_inc(v_size_126_);
lean_dec(v_m_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_170_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v_fold_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v_bkt_144_; uint8_t v___x_145_; 
v___x_131_ = lean_array_get_size(v_buckets_127_);
v___x_132_ = lean_uint64_of_nat(v_a_124_);
v___x_133_ = 32ULL;
v___x_134_ = lean_uint64_shift_right(v___x_132_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v___x_132_, v___x_134_);
v___x_136_ = 16ULL;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_131_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v_bkt_144_ = lean_array_uget_borrowed(v_buckets_127_, v___x_143_);
v___x_145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_124_, v_bkt_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v_size_x27_147_; lean_object* v___x_148_; lean_object* v_buckets_x27_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v_size_x27_147_ = lean_nat_add(v_size_126_, v___x_146_);
lean_dec(v_size_126_);
lean_inc(v_bkt_144_);
v___x_148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_148_, 0, v_a_124_);
lean_ctor_set(v___x_148_, 1, v_b_125_);
lean_ctor_set(v___x_148_, 2, v_bkt_144_);
v_buckets_x27_149_ = lean_array_uset(v_buckets_127_, v___x_143_, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(4u);
v___x_151_ = lean_nat_mul(v_size_x27_147_, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(3u);
v___x_153_ = lean_nat_div(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_array_get_size(v_buckets_x27_149_);
v___x_155_ = lean_nat_dec_le(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v_val_156_; lean_object* v___x_158_; 
v_val_156_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_buckets_x27_149_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v_val_156_);
lean_ctor_set(v___x_129_, 0, v_size_x27_147_);
v___x_158_ = v___x_129_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_size_x27_147_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_val_156_);
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
lean_object* v___x_161_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v_buckets_x27_149_);
lean_ctor_set(v___x_129_, 0, v_size_x27_147_);
v___x_161_ = v___x_129_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_size_x27_147_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_buckets_x27_149_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
lean_object* v___x_163_; lean_object* v_buckets_x27_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_inc(v_bkt_144_);
v___x_163_ = lean_box(0);
v_buckets_x27_164_ = lean_array_uset(v_buckets_127_, v___x_143_, v___x_163_);
v___x_165_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_124_, v_b_125_, v_bkt_144_);
v___x_166_ = lean_array_uset(v_buckets_x27_164_, v___x_143_, v___x_165_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_166_);
v___x_168_ = v___x_129_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_size_126_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(lean_object* v_as_171_, size_t v_i_172_, size_t v_stop_173_, lean_object* v_b_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_usize_dec_eq(v_i_172_, v_stop_173_);
if (v___x_175_ == 0)
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_192_; 
v_fst_176_ = lean_ctor_get(v_b_174_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_b_174_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v_b_174_);
v___x_178_ = lean_array_uget(v_as_171_, v_i_172_);
v_snd_179_ = lean_ctor_get(v___x_178_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_193_);
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_fst_176_, v___x_183_);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_snd_177_, v_snd_179_, v_fst_176_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_185_);
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_187_ = v___x_181_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
size_t v___x_188_; size_t v___x_189_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_172_, v___x_188_);
v_i_172_ = v___x_189_;
v_b_174_ = v___x_187_;
goto _start;
}
}
}
else
{
return v_b_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2___boxed(lean_object* v_as_194_, lean_object* v_i_195_, lean_object* v_stop_196_, lean_object* v_b_197_){
_start:
{
size_t v_i_boxed_198_; size_t v_stop_boxed_199_; lean_object* v_res_200_; 
v_i_boxed_198_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_stop_boxed_199_ = lean_unbox_usize(v_stop_196_);
lean_dec(v_stop_196_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v_as_194_, v_i_boxed_198_, v_stop_boxed_199_, v_b_197_);
lean_dec_ref(v_as_194_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(lean_object* v_as_201_, lean_object* v_i_202_, lean_object* v_j_203_, lean_object* v_bs_204_){
_start:
{
lean_object* v_zero_205_; uint8_t v_isZero_206_; 
v_zero_205_ = lean_unsigned_to_nat(0u);
v_isZero_206_ = lean_nat_dec_eq(v_i_202_, v_zero_205_);
if (v_isZero_206_ == 1)
{
lean_dec(v_j_203_);
lean_dec(v_i_202_);
return v_bs_204_;
}
else
{
lean_object* v_one_207_; lean_object* v_n_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_one_207_ = lean_unsigned_to_nat(1u);
v_n_208_ = lean_nat_sub(v_i_202_, v_one_207_);
lean_dec(v_i_202_);
v___x_209_ = lean_array_fget_borrowed(v_as_201_, v_j_203_);
lean_inc(v_j_203_);
lean_inc(v___x_209_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v_j_203_);
v___x_211_ = lean_nat_add(v_j_203_, v_one_207_);
lean_dec(v_j_203_);
v___x_212_ = lean_array_push(v_bs_204_, v___x_210_);
v_i_202_ = v_n_208_;
v_j_203_ = v___x_211_;
v_bs_204_ = v___x_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg___boxed(lean_object* v_as_214_, lean_object* v_i_215_, lean_object* v_j_216_, lean_object* v_bs_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(v_as_214_, v_i_215_, v_j_216_, v_bs_217_);
lean_dec_ref(v_as_214_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_fst_221_; lean_object* v_fst_222_; uint8_t v___x_223_; 
v_fst_221_ = lean_ctor_get(v_x_219_, 0);
v_fst_222_ = lean_ctor_get(v_x_220_, 0);
v___x_223_ = lean_expr_lt(v_fst_221_, v_fst_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_224_, v_x_225_);
lean_dec_ref(v_x_225_);
lean_dec_ref(v_x_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(lean_object* v_as_229_, lean_object* v_lo_230_, lean_object* v_hi_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_nat_dec_lt(v_lo_230_, v_hi_231_);
if (v___x_232_ == 0)
{
lean_dec(v_lo_230_);
return v_as_229_;
}
else
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v_fst_235_; lean_object* v_snd_236_; uint8_t v___x_237_; 
v___f_233_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___closed__0));
lean_inc(v_lo_230_);
v___x_234_ = l_Array_qpartition___redArg(v_as_229_, v___f_233_, v_lo_230_, v_hi_231_);
v_fst_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_fst_235_);
v_snd_236_ = lean_ctor_get(v___x_234_, 1);
lean_inc(v_snd_236_);
lean_dec_ref(v___x_234_);
v___x_237_ = lean_nat_dec_le(v_hi_231_, v_fst_235_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_snd_236_, v_lo_230_, v_fst_235_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_fst_235_, v___x_239_);
lean_dec(v_fst_235_);
v_as_229_ = v___x_238_;
v_lo_230_ = v___x_240_;
goto _start;
}
else
{
lean_dec(v_fst_235_);
lean_dec(v_lo_230_);
return v_snd_236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(lean_object* v_as_242_, lean_object* v_lo_243_, lean_object* v_hi_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_as_242_, v_lo_243_, v_hi_244_);
lean_dec(v_hi_244_);
return v_res_245_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__0(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_unsigned_to_nat(16u);
v___x_248_ = lean_mk_array(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__1(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_Lean_sortExprs___closed__0, &l_Lean_sortExprs___closed__0_once, _init_l_Lean_sortExprs___closed__0);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_sortExprs___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs(lean_object* v_es_255_, uint8_t v_lt_256_){
_start:
{
lean_object* v___y_258_; lean_object* v_snd_259_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_269_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_es_285_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_291_; lean_object* v___y_292_; 
v___x_282_ = lean_array_get_size(v_es_255_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_mk_empty_array_with_capacity(v___x_282_);
v_es_285_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(v_es_255_, v___x_282_, v___x_283_, v___x_284_);
if (v_lt_256_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_es_285_);
v___x_295_ = lean_nat_dec_eq(v___x_294_, v___x_283_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___y_299_; uint8_t v___x_301_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_sub(v___x_294_, v___x_296_);
v___x_301_ = lean_nat_dec_le(v___x_283_, v___x_297_);
if (v___x_301_ == 0)
{
lean_inc(v___x_297_);
v___y_299_ = v___x_297_;
goto v___jp_298_;
}
else
{
v___y_299_ = v___x_283_;
goto v___jp_298_;
}
v___jp_298_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_le(v___y_299_, v___x_297_);
if (v___x_300_ == 0)
{
lean_dec(v___x_297_);
lean_inc(v___y_299_);
v___y_287_ = v___y_299_;
v___y_288_ = v___y_299_;
goto v___jp_286_;
}
else
{
v___y_287_ = v___y_299_;
v___y_288_ = v___x_297_;
goto v___jp_286_;
}
}
}
else
{
v___y_269_ = v_es_285_;
goto v___jp_268_;
}
}
else
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_array_get_size(v_es_285_);
v___x_303_ = lean_nat_dec_eq(v___x_302_, v___x_283_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___y_307_; uint8_t v___x_309_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_sub(v___x_302_, v___x_304_);
v___x_309_ = lean_nat_dec_le(v___x_283_, v___x_305_);
if (v___x_309_ == 0)
{
lean_inc(v___x_305_);
v___y_307_ = v___x_305_;
goto v___jp_306_;
}
else
{
v___y_307_ = v___x_283_;
goto v___jp_306_;
}
v___jp_306_:
{
uint8_t v___x_308_; 
v___x_308_ = lean_nat_dec_le(v___y_307_, v___x_305_);
if (v___x_308_ == 0)
{
lean_dec(v___x_305_);
lean_inc(v___y_307_);
v___y_291_ = v___y_307_;
v___y_292_ = v___y_307_;
goto v___jp_290_;
}
else
{
v___y_291_ = v___y_307_;
v___y_292_ = v___x_305_;
goto v___jp_290_;
}
}
}
else
{
v___y_269_ = v_es_285_;
goto v___jp_268_;
}
}
v___jp_257_:
{
size_t v_sz_260_; size_t v___x_261_; lean_object* v_es_262_; lean_object* v___x_263_; 
v_sz_260_ = lean_array_size(v___y_258_);
v___x_261_ = ((size_t)0ULL);
v_es_262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_260_, v___x_261_, v___y_258_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_es_262_);
lean_ctor_set(v___x_263_, 1, v_snd_259_);
return v___x_263_;
}
v___jp_264_:
{
lean_object* v_snd_267_; 
v_snd_267_ = lean_ctor_get(v___y_266_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v___y_266_);
v___y_258_ = v___y_265_;
v_snd_259_ = v_snd_267_;
goto v___jp_257_;
}
v___jp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_obj_once(&l_Lean_sortExprs___closed__1, &l_Lean_sortExprs___closed__1_once, _init_l_Lean_sortExprs___closed__1);
v___x_272_ = lean_array_get_size(v___y_269_);
v___x_273_ = lean_nat_dec_lt(v___x_270_, v___x_272_);
if (v___x_273_ == 0)
{
v___y_258_ = v___y_269_;
v_snd_259_ = v___x_271_;
goto v___jp_257_;
}
else
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_obj_once(&l_Lean_sortExprs___closed__2, &l_Lean_sortExprs___closed__2_once, _init_l_Lean_sortExprs___closed__2);
v___x_275_ = lean_nat_dec_le(v___x_272_, v___x_272_);
if (v___x_275_ == 0)
{
if (v___x_273_ == 0)
{
v___y_258_ = v___y_269_;
v_snd_259_ = v___x_271_;
goto v___jp_257_;
}
else
{
size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = ((size_t)0ULL);
v___x_277_ = lean_usize_of_nat(v___x_272_);
v___x_278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_269_, v___x_276_, v___x_277_, v___x_274_);
v___y_265_ = v___y_269_;
v___y_266_ = v___x_278_;
goto v___jp_264_;
}
}
else
{
size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = ((size_t)0ULL);
v___x_280_ = lean_usize_of_nat(v___x_272_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_269_, v___x_279_, v___x_280_, v___x_274_);
v___y_265_ = v___y_269_;
v___y_266_ = v___x_281_;
goto v___jp_264_;
}
}
}
v___jp_286_:
{
lean_object* v___x_289_; 
v___x_289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_es_285_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
v___y_269_ = v___x_289_;
goto v___jp_268_;
}
v___jp_290_:
{
lean_object* v___x_293_; 
v___x_293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_es_285_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
v___y_269_ = v___x_293_;
goto v___jp_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_sortExprs___boxed(lean_object* v_es_310_, lean_object* v_lt_311_){
_start:
{
uint8_t v_lt_boxed_312_; lean_object* v_res_313_; 
v_lt_boxed_312_ = lean_unbox(v_lt_311_);
v_res_313_ = l_Lean_sortExprs(v_es_310_, v_lt_boxed_312_);
lean_dec_ref(v_es_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(lean_object* v_00_u03b2_314_, lean_object* v_m_315_, lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_m_315_, v_a_316_, v_b_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_j_321_, lean_object* v_inv_322_, lean_object* v_bs_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(v_as_319_, v_i_320_, v_j_321_, v_bs_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___boxed(lean_object* v_as_325_, lean_object* v_i_326_, lean_object* v_j_327_, lean_object* v_inv_328_, lean_object* v_bs_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(v_as_325_, v_i_326_, v_j_327_, v_inv_328_, v_bs_329_);
lean_dec_ref(v_as_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(lean_object* v_n_331_, lean_object* v_as_332_, lean_object* v_lo_333_, lean_object* v_hi_334_, lean_object* v_w_335_, lean_object* v_hlo_336_, lean_object* v_hhi_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_as_332_, v_lo_333_, v_hi_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(lean_object* v_n_339_, lean_object* v_as_340_, lean_object* v_lo_341_, lean_object* v_hi_342_, lean_object* v_w_343_, lean_object* v_hlo_344_, lean_object* v_hhi_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(v_n_339_, v_as_340_, v_lo_341_, v_hi_342_, v_w_343_, v_hlo_344_, v_hhi_345_);
lean_dec(v_hi_342_);
lean_dec(v_n_339_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(lean_object* v_n_347_, lean_object* v_as_348_, lean_object* v_lo_349_, lean_object* v_hi_350_, lean_object* v_w_351_, lean_object* v_hlo_352_, lean_object* v_hhi_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_as_348_, v_lo_349_, v_hi_350_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(lean_object* v_n_355_, lean_object* v_as_356_, lean_object* v_lo_357_, lean_object* v_hi_358_, lean_object* v_w_359_, lean_object* v_hlo_360_, lean_object* v_hhi_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(v_n_355_, v_as_356_, v_lo_357_, v_hi_358_, v_w_359_, v_hlo_360_, v_hhi_361_);
lean_dec(v_hi_358_);
lean_dec(v_n_355_);
return v_res_362_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(lean_object* v_00_u03b2_363_, lean_object* v_a_364_, lean_object* v_x_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_364_, v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_367_, lean_object* v_a_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_367_, v_a_368_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v_a_368_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(lean_object* v_00_u03b2_372_, lean_object* v_data_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_data_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(lean_object* v_00_u03b2_375_, lean_object* v_a_376_, lean_object* v_b_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_376_, v_b_377_, v_x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_380_, lean_object* v_i_381_, lean_object* v_source_382_, lean_object* v_target_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v_i_381_, v_source_382_, v_target_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_x_386_, v_x_387_);
return v___x_388_;
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
